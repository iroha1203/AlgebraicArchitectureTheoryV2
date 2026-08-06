#!/usr/bin/env python3
"""Exact finite search for the G-104 incidence condition.

The program deliberately uses only the Python standard library.  All linear
algebra is performed over ``fractions.Fraction`` so that an ``iso`` verdict is
not a floating-point rank heuristic.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Q = Fraction


@dataclass(frozen=True)
class Matrix:
    """A small exact matrix with dimensions retained for empty matrices."""

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
        return Matrix(rows, cols, tuple(tuple(Q(0) for _ in range(cols)) for _ in range(rows)))

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
    def from_mutable(rows: Sequence[Sequence[int | Q]], cols: int | None = None) -> "Matrix":
        row_count = len(rows)
        if row_count:
            column_count = len(rows[0])
        elif cols is not None:
            column_count = cols
        else:
            column_count = 0
        return Matrix(
            row_count,
            column_count,
            tuple(tuple(Q(value) for value in row) for row in rows),
        )

    def __matmul__(self, other: "Matrix") -> "Matrix":
        if self.cols != other.rows:
            raise ValueError("matrix dimensions do not compose")
        if self.rows == 0:
            return Matrix.zero(0, other.cols)
        data = []
        for row in range(self.rows):
            data.append(
                [
                    sum(
                        (self.entries[row][middle] * other.entries[middle][col]
                         for middle in range(self.cols)),
                        Q(0),
                    )
                    for col in range(other.cols)
                ]
            )
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
        """Return a matrix whose columns form a basis of this matrix's kernel."""

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
            [[vectors[col][row] for col in range(len(vectors))] for row in range(self.cols)],
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
        rows = left.rows * right.rows
        cols = left.cols * right.cols
        data = [[Q(0) for _ in range(cols)] for _ in range(rows)]
        for left_row in range(left.rows):
            for left_col in range(left.cols):
                scalar = left.entries[left_row][left_col]
                if scalar == 0:
                    continue
                for right_row in range(right.rows):
                    for right_col in range(right.cols):
                        data[left_row * right.rows + right_row][
                            left_col * right.cols + right_col
                        ] = scalar * right.entries[right_row][right_col]
        return Matrix.from_mutable(data, cols=cols)


@dataclass(frozen=True)
class Nerve:
    """A finite oriented two-dimensional incidence nerve."""

    vertices: int
    edges: tuple[tuple[int, int], ...]
    faces: tuple[tuple[int, int, int], ...]

    def __post_init__(self) -> None:
        if self.vertices < 0:
            raise ValueError("negative vertex count")
        if any(not (0 <= left < self.vertices and 0 <= right < self.vertices)
               for left, right in self.edges):
            raise ValueError("edge endpoint outside the vertex set")
        if any(not all(0 <= edge < len(self.edges) for edge in face) for face in self.faces):
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
        if any(not (0 <= vertex < self.coarse.vertices) for vertex in self.vertex_map):
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
            fine_boundary = self.fine.faces[fine_face]
            mapped_boundary = tuple(self.edge_map[edge] for edge in fine_boundary)
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
    """Compute an induced H1 map from an exact three-term cochain map."""

    if not (coarse_d1 @ coarse_d0).is_zero():
        raise ValueError("coarse coefficient data is not a cochain complex")
    if not (fine_d1 @ fine_d0).is_zero():
        raise ValueError("fine coefficient data is not a cochain complex")
    if fine_d0 @ pullback0 != pullback1 @ coarse_d0:
        raise ValueError("degree-zero square is not a cochain map")
    if fine_d1 @ pullback1 != pullback2 @ coarse_d1:
        raise ValueError("degree-one square is not a cochain map")

    coarse_cycles = coarse_d1.kernel_basis()
    mapped_cycles = pullback1 @ coarse_cycles
    if not (fine_d1 @ mapped_cycles).is_zero():
        raise AssertionError("cochain map sent a cycle outside the fine kernel")

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


def analyze_h1(
    morphism: NerveMorphism,
    coefficient_map: Matrix,
) -> H1Analysis:
    """Compute the induced H1 map for a cell-independent coefficient map.

    ``coefficient_map`` is fine-rank by coarse-rank and is used on every cell.
    This covers the generated-coordinate normal form used by the three Lean
    calibration witnesses and lets the independence fixtures vary dimensions.
    """

    coarse_rank = coefficient_map.cols
    fine_rank = coefficient_map.rows
    coarse_identity = Matrix.identity(coarse_rank)
    fine_identity = Matrix.identity(fine_rank)

    coarse_d0 = Matrix.kronecker(morphism.coarse.d0(), coarse_identity)
    coarse_d1 = Matrix.kronecker(morphism.coarse.d1(), coarse_identity)
    fine_d0 = Matrix.kronecker(morphism.fine.d0(), fine_identity)
    fine_d1 = Matrix.kronecker(morphism.fine.d1(), fine_identity)

    pullback0 = Matrix.kronecker(morphism.cell_pullback(0), coefficient_map)
    pullback1 = Matrix.kronecker(morphism.cell_pullback(1), coefficient_map)
    pullback2 = Matrix.kronecker(morphism.cell_pullback(2), coefficient_map)

    return analyze_complex_map(
        coarse_d0=coarse_d0,
        coarse_d1=coarse_d1,
        fine_d0=fine_d0,
        fine_d1=fine_d1,
        pullback0=pullback0,
        pullback1=pullback1,
        pullback2=pullback2,
    )


@dataclass(frozen=True)
class SupportedNerve:
    """A coordinate-generated coefficient system with cellwise dimensions.

    A cell has one copy of Q for each coordinate in its support.  Endpoint and
    boundary maps are the canonical zero/identity coordinate restrictions.
    Hence dimensions may vary cell by cell while ``d1 * d0 = 0`` remains an
    exact incidence assertion rather than an assumed matrix equation.
    """

    nerve: Nerve
    coordinate_count: int
    chart_supports: tuple[frozenset[int], ...]
    edge_supports: tuple[frozenset[int], ...]
    face_supports: tuple[frozenset[int], ...]

    def __post_init__(self) -> None:
        universe = set(range(self.coordinate_count))
        if self.coordinate_count <= 0:
            raise ValueError("a supported nerve needs at least one coordinate")
        if len(self.chart_supports) != self.nerve.vertices:
            raise ValueError("chart-support profile has the wrong size")
        if len(self.edge_supports) != len(self.nerve.edges):
            raise ValueError("edge-support profile has the wrong size")
        if len(self.face_supports) != len(self.nerve.faces):
            raise ValueError("face-support profile has the wrong size")
        if any(not support or not set(support) <= universe for support in self.chart_supports):
            raise ValueError("chart supports must be nonempty subsets of the coordinate universe")
        if any(not set(support) <= universe for support in self.edge_supports + self.face_supports):
            raise ValueError("cell support leaves the coordinate universe")
        for edge, (left, right) in enumerate(self.nerve.edges):
            if not self.edge_supports[edge] <= (
                self.chart_supports[left] & self.chart_supports[right]
            ):
                raise ValueError("edge support is not contained in both endpoint supports")
        for face, boundary in enumerate(self.nerve.faces):
            common = set(range(self.coordinate_count))
            for edge in boundary:
                common &= self.edge_supports[edge]
            if not set(self.face_supports[face]) <= common:
                raise ValueError("face support is not contained in every boundary-edge support")
        if not (self.d1() @ self.d0()).is_zero():
            raise AssertionError("coordinate incidence failed d1 * d0 = 0")

    def supports(self, dimension: int) -> tuple[frozenset[int], ...]:
        if dimension == 0:
            return self.chart_supports
        if dimension == 1:
            return self.edge_supports
        if dimension == 2:
            return self.face_supports
        raise ValueError("only dimensions zero through two are supported")

    def basis(self, dimension: int) -> tuple[tuple[int, int], ...]:
        return tuple(
            (cell, coordinate)
            for cell, support in enumerate(self.supports(dimension))
            for coordinate in sorted(support)
        )

    def d0(self) -> Matrix:
        chart_basis = self.basis(0)
        edge_basis = self.basis(1)
        chart_index = {basis: index for index, basis in enumerate(chart_basis)}
        data = [[Q(0) for _ in chart_basis] for _ in edge_basis]
        for row, (edge, coordinate) in enumerate(edge_basis):
            left, right = self.nerve.edges[edge]
            data[row][chart_index[(left, coordinate)]] -= 1
            data[row][chart_index[(right, coordinate)]] += 1
        return Matrix.from_mutable(data, cols=len(chart_basis))

    def d1(self) -> Matrix:
        edge_basis = self.basis(1)
        face_basis = self.basis(2)
        edge_index = {basis: index for index, basis in enumerate(edge_basis)}
        data = [[Q(0) for _ in edge_basis] for _ in face_basis]
        for row, (face, coordinate) in enumerate(face_basis):
            edge0, edge1, edge2 = self.nerve.faces[face]
            data[row][edge_index[(edge0, coordinate)]] += 1
            data[row][edge_index[(edge1, coordinate)]] -= 1
            data[row][edge_index[(edge2, coordinate)]] += 1
        return Matrix.from_mutable(data, cols=len(edge_basis))

    def dimensions(self) -> dict[str, list[int]]:
        return {
            "charts": [len(support) for support in self.chart_supports],
            "edges": [len(support) for support in self.edge_supports],
            "faces": [len(support) for support in self.face_supports],
        }


def supported_pullback(
    morphism: NerveMorphism,
    coarse: SupportedNerve,
    fine: SupportedNerve,
    coordinate_map: tuple[int, ...],
    dimension: int,
) -> Matrix:
    if coarse.nerve != morphism.coarse or fine.nerve != morphism.fine:
        raise ValueError("supported nerves do not match their incidence morphism")
    if len(coordinate_map) != fine.coordinate_count:
        raise ValueError("supported coordinate map has the wrong size")
    if any(not 0 <= coordinate < coarse.coordinate_count for coordinate in coordinate_map):
        raise ValueError("supported coordinate map leaves the coarse universe")

    if dimension == 0:
        cell_map: Sequence[int | None] = morphism.vertex_map
    elif dimension == 1:
        cell_map = morphism.edge_map
    elif dimension == 2:
        cell_map = morphism.face_map
    else:
        raise ValueError("only dimensions zero through two are supported")

    coarse_basis = coarse.basis(dimension)
    fine_basis = fine.basis(dimension)
    coarse_index = {basis: index for index, basis in enumerate(coarse_basis)}
    data = [[Q(0) for _ in coarse_basis] for _ in fine_basis]
    for row, (fine_cell, fine_coordinate) in enumerate(fine_basis):
        coarse_cell = cell_map[fine_cell]
        if coarse_cell is None:
            continue
        coarse_basis_element = (coarse_cell, coordinate_map[fine_coordinate])
        if coarse_basis_element not in coarse_index:
            raise ValueError("fine cell support is not compatible with its mapped coarse cell")
        data[row][coarse_index[coarse_basis_element]] = Q(1)
    return Matrix.from_mutable(data, cols=len(coarse_basis))


def analyze_supported_h1(
    morphism: NerveMorphism,
    coarse: SupportedNerve,
    fine: SupportedNerve,
    coordinate_map: tuple[int, ...],
) -> H1Analysis:
    return analyze_complex_map(
        coarse_d0=coarse.d0(),
        coarse_d1=coarse.d1(),
        fine_d0=fine.d0(),
        fine_d1=fine.d1(),
        pullback0=supported_pullback(morphism, coarse, fine, coordinate_map, 0),
        pullback1=supported_pullback(morphism, coarse, fine, coordinate_map, 1),
        pullback2=supported_pullback(morphism, coarse, fine, coordinate_map, 2),
    )


@lru_cache(maxsize=None)
def nerve_h1_dimension(nerve: Nerve) -> int:
    return nerve.d1().kernel_basis().cols - nerve.d0().rank()


def connected(vertices: Iterable[int], edges: Iterable[tuple[int, int]]) -> bool:
    vertex_set = set(vertices)
    if not vertex_set:
        return False
    adjacency = {vertex: set() for vertex in vertex_set}
    for left, right in edges:
        if left in vertex_set and right in vertex_set:
            adjacency[left].add(right)
            adjacency[right].add(left)
    reached = {next(iter(vertex_set))}
    frontier = list(reached)
    while frontier:
        current = frontier.pop()
        for neighbour in adjacency[current] - reached:
            reached.add(neighbour)
            frontier.append(neighbour)
    return reached == vertex_set


def condition_vector(morphism: NerveMorphism, *, c0: bool = True) -> dict[str, bool]:
    """Evaluate C0--C5 and self-loop endpoint reflection.

    C0 is supplied by the coefficient/support fixture.  The normal-form search
    uses full supports and therefore passes ``c0=True``.  The other clauses are
    computed directly from incidence data.  C3 is *stated* as cycle span by
    face boundaries; exact rank is only its finite decision procedure, not a
    cohomology premise added to the candidate.
    """

    fibers = [
        tuple(index for index, mapped in enumerate(morphism.vertex_map) if mapped == coarse)
        for coarse in range(morphism.coarse.vertices)
    ]
    c1 = all(
        connected(
            fiber,
            (
                edge for edge in morphism.fine.edges
                if edge[0] in fiber and edge[1] in fiber
            ),
        )
        for fiber in fibers
    )
    c2 = all(coarse in morphism.edge_map for coarse in range(len(morphism.coarse.edges)))

    c3 = True
    for fiber in fibers:
        fiber_vertices = {vertex: local for local, vertex in enumerate(fiber)}
        selected_edges = [
            edge for edge, (left, right) in enumerate(morphism.fine.edges)
            if left in fiber_vertices and right in fiber_vertices
        ]
        edge_index = {edge: local for local, edge in enumerate(selected_edges)}
        local_edges = tuple(
            (
                fiber_vertices[morphism.fine.edges[edge][0]],
                fiber_vertices[morphism.fine.edges[edge][1]],
            )
            for edge in selected_edges
        )
        local_faces = tuple(
            tuple(edge_index[edge] for edge in face)
            for face in morphism.fine.faces
            if all(edge in edge_index for edge in face)
        )
        local_nerve = Nerve(len(fiber), local_edges, local_faces)
        if nerve_h1_dimension(local_nerve) != 0:
            c3 = False
            break

    c4 = all(coarse in morphism.face_map for coarse in range(len(morphism.coarse.faces)))
    nondegenerate_edges = [edge for edge in morphism.edge_map if edge is not None]
    c5 = len(nondegenerate_edges) == len(set(nondegenerate_edges))
    reflection = all(
        morphism.coarse.edges[coarse][0] != morphism.coarse.edges[coarse][1]
        or morphism.fine.edges[fine][0] == morphism.fine.edges[fine][1]
        for fine, coarse in enumerate(morphism.edge_map)
        if coarse is not None
    )
    return {
        "C0_chart_support_image": c0,
        "C1_chart_fiber_connected": c1,
        "C2_coarse_edge_lift": c2,
        "C3_fiber_cycles_filled": c3,
        "C4_coarse_face_lift": c4,
        "C5_unique_coarse_edge_lift": c5,
        "R_self_loop_endpoint_reflection": reflection,
    }


@dataclass(frozen=True)
class SearchCase:
    name: str
    morphism: NerveMorphism
    coefficient_map: Matrix
    fine_to_coarse_coordinate: tuple[int, ...] = ()
    coarse_chart_supports: tuple[frozenset[int], ...] | None = None
    fine_chart_supports: tuple[frozenset[int], ...] | None = None

    def c0_holds(self) -> bool:
        coordinate_map = self.fine_to_coarse_coordinate
        if not coordinate_map:
            if self.coefficient_map.rows != self.coefficient_map.cols:
                raise ValueError("a non-square coefficient fixture needs an explicit coordinate map")
            coordinate_map = tuple(range(self.coefficient_map.rows))
        if len(coordinate_map) != self.coefficient_map.rows:
            raise ValueError("coordinate map has the wrong fine rank")
        if any(not 0 <= coordinate < self.coefficient_map.cols for coordinate in coordinate_map):
            raise ValueError("coordinate map leaves the coarse coordinate set")

        coarse_supports = self.coarse_chart_supports or tuple(
            frozenset(range(self.coefficient_map.cols))
            for _ in range(self.morphism.coarse.vertices)
        )
        fine_supports = self.fine_chart_supports or tuple(
            frozenset(range(self.coefficient_map.rows))
            for _ in range(self.morphism.fine.vertices)
        )
        if len(coarse_supports) != self.morphism.coarse.vertices:
            raise ValueError("coarse chart-support profile has the wrong size")
        if len(fine_supports) != self.morphism.fine.vertices:
            raise ValueError("fine chart-support profile has the wrong size")

        for fine_chart, support in enumerate(fine_supports):
            coarse_chart = self.morphism.vertex_map[fine_chart]
            image = {coordinate_map[coordinate] for coordinate in support}
            if not image <= coarse_supports[coarse_chart]:
                raise ValueError("fine chart support is not compatible with its coarse image")

        return all(
            coarse_supports[coarse_chart]
            == {
                coordinate_map[coordinate]
                for fine_chart, mapped_chart in enumerate(self.morphism.vertex_map)
                if mapped_chart == coarse_chart
                for coordinate in fine_supports[fine_chart]
            }
            for coarse_chart in range(self.morphism.coarse.vertices)
        )

    def result(self) -> dict[str, object]:
        return {
            "name": self.name,
            "conditions": condition_vector(self.morphism, c0=self.c0_holds()),
            "h1": asdict(analyze_h1(self.morphism, self.coefficient_map)),
            "sizes": {
                "coarse": {
                    "charts": self.morphism.coarse.vertices,
                    "edges": len(self.morphism.coarse.edges),
                    "faces": len(self.morphism.coarse.faces),
                    "coefficient_rank": self.coefficient_map.cols,
                },
                "fine": {
                    "charts": self.morphism.fine.vertices,
                    "edges": len(self.morphism.fine.edges),
                    "faces": len(self.morphism.fine.faces),
                    "coefficient_rank": self.coefficient_map.rows,
                },
            },
        }


def calibration_cases() -> tuple[SearchCase, ...]:
    """Exact Python reconstructions of the three reviewed Lean obstructions."""

    coordinate_identity = Matrix.identity(3)

    coarse_triangle = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2)),
        ((0, 1, 2),),
    )
    face_fine = Nerve(
        4,
        ((0, 1), (1, 2), (0, 3), (2, 3)),
        (),
    )
    face = NerveMorphism(
        coarse_triangle,
        face_fine,
        (0, 0, 1, 2),
        (None, 0, 1, 2),
        (),
    )

    edge_fine = Nerve(
        3,
        ((0, 1), (0, 1), (0, 2), (1, 2)),
        ((0, 2, 3),),
    )
    edge = NerveMorphism(
        coarse_triangle,
        edge_fine,
        (0, 1, 2),
        (0, 0, 1, 2),
        (0,),
    )

    loop_coarse = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2), (0, 0), (0, 1)),
        ((0, 1, 2),),
    )
    loop_fine = Nerve(
        5,
        ((0, 3), (0, 4), (3, 4), (0, 1), (1, 2), (0, 3)),
        ((0, 1, 2),),
    )
    loop = NerveMorphism(
        loop_coarse,
        loop_fine,
        (0, 0, 0, 1, 2),
        (0, 1, 2, 3, None, 4),
        (0,),
    )

    return (
        SearchCase("FaceLiftObstruction", face, coordinate_identity),
        SearchCase("EdgeFiberObstruction", edge, coordinate_identity),
        SearchCase("LoopLiftObstruction", loop, coordinate_identity),
    )


def positive_case() -> SearchCase:
    """A nondegenerate firing witness for the revised candidate."""

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
    morphism = NerveMorphism(
        coarse,
        fine,
        (0, 0, 1, 2),
        (None, 0, 1, 2, 3),
        (0,),
    )
    return SearchCase("nondegenerate_positive", morphism, Matrix.identity(2))


def supported_incidence_morphism() -> NerveMorphism:
    """A nondegenerate incidence comparison with two surviving coarse cycles."""

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
    return NerveMorphism(
        coarse,
        fine,
        (0, 0, 1, 2),
        (None, 0, 1, 2, 3, 4),
        (0,),
    )


def full_supported_nerve(nerve: Nerve, coordinate_count: int = 1) -> SupportedNerve:
    full = frozenset(range(coordinate_count))
    return SupportedNerve(
        nerve=nerve,
        coordinate_count=coordinate_count,
        chart_supports=tuple(full for _ in range(nerve.vertices)),
        edge_supports=tuple(full for _ in nerve.edges),
        face_supports=tuple(full for _ in nerve.faces),
    )


def supported_c0_holds(
    morphism: NerveMorphism,
    coarse: SupportedNerve,
    fine: SupportedNerve,
    coordinate_map: tuple[int, ...],
) -> bool:
    return all(
        coarse.chart_supports[coarse_chart]
        == frozenset(
            coordinate_map[coordinate]
            for fine_chart, mapped_chart in enumerate(morphism.vertex_map)
            if mapped_chart == coarse_chart
            for coordinate in fine.chart_supports[fine_chart]
        )
        for coarse_chart in range(morphism.coarse.vertices)
    )


def supported_result(
    name: str,
    morphism: NerveMorphism,
    coarse: SupportedNerve,
    fine: SupportedNerve,
) -> dict[str, object]:
    coordinate_map = tuple(0 for _ in range(fine.coordinate_count))
    analysis = analyze_supported_h1(morphism, coarse, fine, coordinate_map)
    conditions = condition_vector(
        morphism,
        c0=supported_c0_holds(morphism, coarse, fine, coordinate_map),
    )
    return {
        "name": name,
        "conditions": conditions,
        "coarse_cell_dimensions": coarse.dimensions(),
        "fine_cell_dimensions": fine.dimensions(),
        "cell_maps": "canonical zero/identity restrictions for the single free coordinate",
        "h1": asdict(analysis),
    }


def cellwise_coefficient_search() -> dict[str, object]:
    """Exhaust all 0/1 fine cell dimensions on one fixed positive incidence map."""

    morphism = supported_incidence_morphism()
    conditions = condition_vector(morphism)
    if not all(conditions.values()):
        raise AssertionError("cellwise coefficient sweep did not start from candidate incidence")

    coarse = full_supported_nerve(morphism.coarse)
    unit = frozenset((0,))
    empty = frozenset()
    chart_supports = tuple(unit for _ in range(morphism.fine.vertices))
    systems = 0
    isomorphisms = 0
    nonisomorphisms = 0
    both_h1_nonzero = 0
    counterexamples: list[dict[str, object]] = []

    for edge_bits in product((False, True), repeat=len(morphism.fine.edges)):
        edge_supports = tuple(unit if bit else empty for bit in edge_bits)
        face_options: list[tuple[frozenset[int], ...]] = []
        for face in morphism.fine.faces:
            if all(edge_bits[edge] for edge in face):
                face_options.append((empty, unit))
            else:
                face_options.append((empty,))
        for selected_faces in product(*face_options):
            fine = SupportedNerve(
                nerve=morphism.fine,
                coordinate_count=1,
                chart_supports=chart_supports,
                edge_supports=edge_supports,
                face_supports=tuple(selected_faces),
            )
            systems += 1
            analysis = analyze_supported_h1(morphism, coarse, fine, (0,))
            if analysis.isomorphism:
                isomorphisms += 1
            else:
                nonisomorphisms += 1
                if analysis.coarse_h1_dimension > 0 and analysis.fine_h1_dimension > 0:
                    both_h1_nonzero += 1
                if len(counterexamples) < 12:
                    counterexamples.append(
                        {
                            "fine_cell_dimensions": fine.dimensions(),
                            "h1": asdict(analysis),
                        }
                    )

    full_positive = supported_result(
        "same_incidence_full_coordinate_support",
        morphism,
        coarse,
        full_supported_nerve(morphism.fine),
    )
    hole_fine = SupportedNerve(
        nerve=morphism.fine,
        coordinate_count=1,
        chart_supports=chart_supports,
        edge_supports=(empty,) + tuple(unit for _ in morphism.fine.edges[1:]),
        face_supports=(unit,),
    )
    hole_counterexample = supported_result(
        "same_incidence_missing_fiber_edge_coordinate",
        morphism,
        coarse,
        hole_fine,
    )
    duplicate_counterexample = supported_result(
        "same_incidence_duplicated_fine_coordinate",
        morphism,
        coarse,
        full_supported_nerve(morphism.fine, coordinate_count=2),
    )

    full_h1 = full_positive["h1"]
    hole_h1 = hole_counterexample["h1"]
    duplicate_h1 = duplicate_counterexample["h1"]
    structural_negative = (
        full_h1["isomorphism"]
        and not hole_h1["isomorphism"]
        and not duplicate_h1["isomorphism"]
        and hole_h1["coarse_h1_dimension"] > 0
        and hole_h1["fine_h1_dimension"] > 0
        and duplicate_h1["coarse_h1_dimension"] > 0
        and duplicate_h1["fine_h1_dimension"] > 0
        and full_positive["conditions"] == hole_counterexample["conditions"]
        and full_positive["conditions"] == duplicate_counterexample["conditions"]
        and all(full_positive["conditions"].values())
    )
    if not structural_negative:
        raise AssertionError("cellwise free-coordinate structural negative did not fire")

    return {
        "bounds": {
            "coordinate_count": 1,
            "chart_dimensions": "fixed at 1 and nonempty",
            "fine_edge_dimensions": "all 0/1 assignments",
            "fine_face_dimensions": "all incidence-compatible 0/1 assignments",
            "coarse_cell_dimensions": "fixed at 1",
            "cell_maps": "canonical zero/identity coordinate restrictions",
        },
        "counts": {
            "supported_coefficient_systems": systems,
            "isomorphisms": isomorphisms,
            "nonisomorphisms": nonisomorphisms,
            "nonisomorphisms_with_both_h1_nonzero": both_h1_nonzero,
        },
        "same_incidence_pair": {
            "positive": full_positive,
            "support_hole_counterexample": hole_counterexample,
            "duplicate_coordinate_counterexample": duplicate_counterexample,
        },
        "sample_counterexamples": counterexamples,
        "structural_negative": structural_negative,
        "mechanism": (
            "The support-hole case keeps the incidence fiber edge but gives it coefficient dimension zero. "
            "The duplicate-coordinate case is universal: duplicating a nonzero fine H1 summand leaves "
            "all incidence predicates unchanged and makes the comparison non-surjective."
        ),
        "law_realizability": "not checked; this is authorized free-coefficient evidence only",
    }


def independence_cases() -> tuple[tuple[str, SearchCase], ...]:
    """One non-isomorphism after dropping each final-candidate clause."""

    identity_incidence = positive_case().morphism.coarse
    c0_morphism = NerveMorphism(
        identity_incidence,
        identity_incidence,
        tuple(range(identity_incidence.vertices)),
        tuple(range(len(identity_incidence.edges))),
        tuple(range(len(identity_incidence.faces))),
    )
    c0_case = SearchCase(
        "drop_C0_support_coordinate",
        c0_morphism,
        Matrix.from_mutable([[1, 0]]),
        fine_to_coarse_coordinate=(0,),
        coarse_chart_supports=tuple(frozenset((0, 1)) for _ in range(c0_morphism.coarse.vertices)),
        fine_chart_supports=tuple(frozenset((0,)) for _ in range(c0_morphism.fine.vertices)),
    )

    c1_coarse = Nerve(2, ((0, 1), (0, 1)), ())
    c1_fine = Nerve(3, ((0, 2), (1, 2)), ())
    c1_case = SearchCase(
        "drop_C1_disconnected_chart_fiber",
        NerveMorphism(c1_coarse, c1_fine, (0, 0, 1), (0, 1), ()),
        Matrix.identity(1),
    )

    c2_fine = Nerve(2, ((0, 1),), ())
    c2_case = SearchCase(
        "drop_C2_missing_parallel_edge_lift",
        NerveMorphism(c1_coarse, c2_fine, (0, 1), (0,), ()),
        Matrix.identity(1),
    )

    c3_coarse = Nerve(1, (), ())
    c3_fine = Nerve(1, ((0, 0), (0, 0)), ())
    c3_case = SearchCase(
        "drop_C3_unfilled_fiber_cycles",
        NerveMorphism(c3_coarse, c3_fine, (0,), (None, None), ()),
        Matrix.identity(1),
    )

    face, edge, loop = calibration_cases()
    return (
        ("C0_chart_support_image", c0_case),
        ("C1_chart_fiber_connected", c1_case),
        ("C2_coarse_edge_lift", c2_case),
        ("C3_fiber_cycles_filled", c3_case),
        ("C4_coarse_face_lift", face),
        ("C5_unique_coarse_edge_lift", edge),
        ("R_self_loop_endpoint_reflection", loop),
    )


def is_connected_nerve(nerve: Nerve) -> bool:
    return connected(range(nerve.vertices), nerve.edges)


def coarse_nerves(max_vertices: int, max_edges: int, max_faces: int) -> Iterator[Nerve]:
    """Enumerate orientation-normalized connected coarse nerves.

    Edges are oriented from the lower chart index to the higher chart index;
    this quotients the irrelevant choice of basis sign.  Parallel edges and
    self-loops remain distinct cells.  At most one face is used by the current
    search, matching the explicit bound in the report.
    """

    if max_faces > 1:
        raise ValueError("the current exhaustive normal form supports at most one coarse face")
    for vertices in range(1, max_vertices + 1):
        edge_types = tuple((left, right) for left in range(vertices) for right in range(left, vertices))
        for edge_count in range(0, max_edges + 1):
            for edges in combinations_with_replacement(edge_types, edge_count):
                no_face = Nerve(vertices, tuple(edges), ())
                if not is_connected_nerve(no_face):
                    continue
                yield no_face
                if max_faces == 0:
                    continue
                for face in product(range(edge_count), repeat=3):
                    try:
                        yield Nerve(vertices, tuple(edges), (tuple(face),))
                    except ValueError:
                        continue


def positive_compositions(total: int, parts: int) -> Iterator[tuple[int, ...]]:
    if parts == 1:
        yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in positive_compositions(total - first, parts - 1):
            yield (first,) + rest


@dataclass(frozen=True)
class FiberLayout:
    fibers: tuple[tuple[int, ...], ...]
    edges: tuple[tuple[int, int], ...]
    faces: tuple[tuple[int, int, int], ...]


def fiber_layouts(sizes: tuple[int, ...]) -> Iterator[FiberLayout]:
    """Connected fiber normal forms: a tree or one explicitly filled cycle."""

    fibers: list[tuple[int, ...]] = []
    cursor = 0
    for size in sizes:
        fibers.append(tuple(range(cursor, cursor + size)))
        cursor += size
    eligible = [index for index, size in enumerate(sizes) if size >= 3]
    for filled_flags in product((False, True), repeat=len(eligible)):
        filled = dict(zip(eligible, filled_flags, strict=True))
        edges: list[tuple[int, int]] = []
        faces: list[tuple[int, int, int]] = []
        for fiber_index, fiber in enumerate(fibers):
            root = fiber[0]
            star_edges: list[int] = []
            for vertex in fiber[1:]:
                star_edges.append(len(edges))
                edges.append((root, vertex))
            if filled.get(fiber_index, False):
                chord = len(edges)
                edges.append((fiber[1], fiber[2]))
                faces.append((star_edges[0], star_edges[1], chord))
        yield FiberLayout(tuple(fibers), tuple(edges), tuple(faces))


def refinement_morphisms(coarse: Nerve, max_fine_vertices: int) -> Iterator[NerveMorphism]:
    """Enumerate all unique edge-lift assignments in the bounded fiber normal form."""

    for fine_vertices in range(coarse.vertices, max_fine_vertices + 1):
        for sizes in positive_compositions(fine_vertices, coarse.vertices):
            for layout in fiber_layouts(sizes):
                choices: list[tuple[tuple[int, int], ...]] = []
                for left, right in coarse.edges:
                    if left == right:
                        choices.append(tuple((vertex, vertex) for vertex in layout.fibers[left]))
                    else:
                        choices.append(
                            tuple(product(layout.fibers[left], layout.fibers[right]))
                        )
                for lifted_edges in product(*choices):
                    fine_edges = layout.edges + tuple(lifted_edges)
                    internal_count = len(layout.edges)
                    mapped_faces = tuple(
                        tuple(internal_count + edge for edge in face)
                        for face in coarse.faces
                    )
                    fine_faces = layout.faces + mapped_faces
                    try:
                        fine = Nerve(fine_vertices, fine_edges, fine_faces)
                        morphism = NerveMorphism(
                            coarse=coarse,
                            fine=fine,
                            vertex_map=tuple(
                                coarse_vertex
                                for coarse_vertex, fiber in enumerate(layout.fibers)
                                for _ in fiber
                            ),
                            edge_map=(None,) * internal_count + tuple(range(len(coarse.edges))),
                            face_map=(None,) * len(layout.faces) + tuple(range(len(coarse.faces))),
                        )
                    except ValueError:
                        continue
                    yield morphism


def exhaustive_search(
    *,
    max_coarse_vertices: int,
    max_coarse_edges: int,
    max_coarse_faces: int,
    max_fine_vertices: int,
    max_coefficient_rank: int,
) -> dict[str, object]:
    coarse_count = 0
    refinement_count = 0
    candidate_count = 0
    coefficient_cases = 0
    counterexamples: list[dict[str, object]] = []
    condition_names = tuple(condition_vector(positive_case().morphism))

    for coarse in coarse_nerves(max_coarse_vertices, max_coarse_edges, max_coarse_faces):
        coarse_count += 1
        for morphism in refinement_morphisms(coarse, max_fine_vertices):
            refinement_count += 1
            conditions = condition_vector(morphism)
            if not all(conditions.values()):
                continue
            candidate_count += 1
            for rank in range(1, max_coefficient_rank + 1):
                coefficient_cases += 1
                analysis = analyze_h1(morphism, Matrix.identity(rank))
                if not analysis.isomorphism:
                    counterexamples.append(
                        {
                            "conditions": conditions,
                            "coarse": asdict(morphism.coarse),
                            "fine": asdict(morphism.fine),
                            "vertex_map": morphism.vertex_map,
                            "edge_map": morphism.edge_map,
                            "face_map": morphism.face_map,
                            "coefficient_rank": rank,
                            "h1": asdict(analysis),
                        }
                    )
                    if len(counterexamples) >= 20:
                        break
            if len(counterexamples) >= 20:
                break
        if len(counterexamples) >= 20:
            break

    return {
        "candidate": list(condition_names),
        "normal_form": {
            "edge_orientation": "lower chart index to higher; orientation sign quotiented",
            "coarse_connected": True,
            "coarse_parallel_edges_and_loops": True,
            "coarse_face_bound": max_coarse_faces,
            "fine_chart_fibers": "positive fibers with a star tree or one explicitly filled triangle",
            "coarse_edge_lifts": "exactly one; every endpoint assignment enumerated; loops reflected",
            "coarse_face_lifts": "one boundary-commuting lift per coarse face",
            "coefficients": "constant free Q-rank, identity coordinate pullback, basis changes quotiented",
        },
        "bounds": {
            "coarse_charts": max_coarse_vertices,
            "coarse_edges": max_coarse_edges,
            "coarse_faces": max_coarse_faces,
            "fine_charts": max_fine_vertices,
            "coefficient_rank": max_coefficient_rank,
        },
        "counts": {
            "coarse_nerves": coarse_count,
            "generated_refinements": refinement_count,
            "candidate_refinements": candidate_count,
            "coefficient_cases": coefficient_cases,
            "counterexamples": len(counterexamples),
        },
        "counterexamples": counterexamples,
    }


def calibration_report() -> list[dict[str, object]]:
    expected = {
        "FaceLiftObstruction": (True, False),
        "EdgeFiberObstruction": (True, False),
        "LoopLiftObstruction": (False, True),
    }
    report = []
    for case in calibration_cases():
        result = case.result()
        analysis = result["h1"]
        observed = (analysis["injective"], analysis["surjective"])
        if observed != expected[case.name]:
            raise AssertionError(
                f"calibration mismatch for {case.name}: {observed} != {expected[case.name]}"
            )
        result["calibration_pass"] = True
        report.append(result)
    return report


def independence_report() -> list[dict[str, object]]:
    report = []
    for dropped, case in independence_cases():
        result = case.result()
        conditions = result["conditions"]
        false_conditions = [name for name, value in conditions.items() if not value]
        if false_conditions != [dropped]:
            raise AssertionError(
                f"{case.name} should drop only {dropped}, observed {false_conditions}"
            )
        if result["h1"]["isomorphism"]:
            raise AssertionError(f"{case.name} did not break the comparison isomorphism")
        result["dropped_clause"] = dropped
        result["independence_pass"] = True
        report.append(result)
    return report


def firing_report() -> dict[str, object]:
    case = positive_case()
    result = case.result()
    morphism = case.morphism
    fibers = [morphism.vertex_map.count(vertex) for vertex in range(morphism.coarse.vertices)]
    firing = {
        "comparison_factor_noninjective": len(set(morphism.vertex_map)) < len(morphism.vertex_map),
        "coarse_h1_nonzero": result["h1"]["coarse_h1_dimension"] > 0,
        "fine_h1_nonzero": result["h1"]["fine_h1_dimension"] > 0,
        "chart_fiber_of_size_at_least_two": max(fibers) >= 2,
        "coarse_face_nonempty": bool(morphism.coarse.faces),
        "fine_degenerate_fiber_edge_exists": any(edge is None for edge in morphism.edge_map),
    }
    if not all(firing.values()) or not result["h1"]["isomorphism"]:
        raise AssertionError("nondegenerate positive fixture failed its firing gate")
    result["firing_gate"] = firing
    result["firing_pass"] = True
    return result


def complete_report(args: argparse.Namespace) -> dict[str, object]:
    calibrations = calibration_report()
    independence = independence_report()
    firing = firing_report()
    coefficient_search = cellwise_coefficient_search()
    search = exhaustive_search(
        max_coarse_vertices=args.max_coarse_vertices,
        max_coarse_edges=args.max_coarse_edges,
        max_coarse_faces=args.max_coarse_faces,
        max_fine_vertices=args.max_fine_vertices,
        max_coefficient_rank=args.max_coefficient_rank,
    )
    return {
        "artifact": "G-104 off-loop condition hunt",
        "arithmetic": "exact rational linear algebra",
        "calibration": calibrations,
        "round_1_constant_coordinate_candidate_search": search,
        "nondegenerate_positive": firing,
        "clause_independence": independence,
        "round_2_cellwise_coefficient_search": coefficient_search,
        "decision": {
            "stop_condition": "B_structural_negative_in_free_coefficient_model",
            "final_candidate": None,
            "reason": (
                "The same nondegenerate incidence data passes C0-C5 plus endpoint reflection "
                "with both an H1 isomorphism and a non-isomorphism.  An incidence-only revision "
                "cannot distinguish the pair; coefficient-generation restrictions must do so."
            ),
            "goal_proof_state_changed": False,
            "law_realizability_checked": False,
        },
        "artifact_gates_pass": (
            not search["counterexamples"]
            and all(item["calibration_pass"] for item in calibrations)
            and all(item["independence_pass"] for item in independence)
            and firing["firing_pass"]
            and coefficient_search["structural_negative"]
        ),
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "command",
        choices=("calibrate", "independence", "firing", "search", "coefficients", "run"),
        nargs="?",
        default="run",
    )
    result.add_argument("--max-coarse-vertices", type=int, default=3)
    result.add_argument("--max-coarse-edges", type=int, default=4)
    result.add_argument("--max-coarse-faces", type=int, default=1)
    result.add_argument("--max-fine-vertices", type=int, default=4)
    result.add_argument("--max-coefficient-rank", type=int, default=2)
    result.add_argument("--output", type=Path)
    return result


def main() -> int:
    args = parser().parse_args()
    if args.command == "calibrate":
        output: object = calibration_report()
    elif args.command == "independence":
        output = independence_report()
    elif args.command == "firing":
        output = firing_report()
    elif args.command == "coefficients":
        output = cellwise_coefficient_search()
    elif args.command == "search":
        output = exhaustive_search(
            max_coarse_vertices=args.max_coarse_vertices,
            max_coarse_edges=args.max_coarse_edges,
            max_coarse_faces=args.max_coarse_faces,
            max_fine_vertices=args.max_fine_vertices,
            max_coefficient_rank=args.max_coefficient_rank,
        )
    else:
        output = complete_report(args)

    rendered = json.dumps(output, ensure_ascii=False, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
