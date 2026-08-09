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
        for edge0, edge1, edge2 in self.faces:
            left0, right0 = self.edges[edge0]
            left1, right1 = self.edges[edge1]
            left2, right2 = self.edges[edge2]
            if not (left0 == left1 and right0 == left2 and right1 == right2):
                raise ValueError(
                    "face boundary violates the three endpoint equalities"
                )
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


def matrix_column(matrix: Matrix, column: int) -> Matrix:
    return Matrix.from_mutable(
        [[matrix.entries[row][column]] for row in range(matrix.rows)],
        cols=1,
    )


def quotient_h1_representatives(d0: Matrix, d1: Matrix) -> Matrix:
    """Choose deterministic cycle representatives modulo the boundary span."""

    cycles = d1.kernel_basis()
    span = d0
    rank = span.rank()
    representatives: list[Matrix] = []
    for column in range(cycles.cols):
        candidate_column = matrix_column(cycles, column)
        candidate_span = Matrix.hstack(span, candidate_column)
        candidate_rank = candidate_span.rank()
        if candidate_rank > rank:
            representatives.append(candidate_column)
            span = candidate_span
            rank = candidate_rank
    expected = cycles.cols - d0.rank()
    if len(representatives) != expected:
        raise AssertionError("failed to choose an H1 quotient basis")
    if not representatives:
        return Matrix.zero(d0.rows, 0)
    result = representatives[0]
    for representative in representatives[1:]:
        result = Matrix.hstack(result, representative)
    return result


def solve_linear_system(matrix: Matrix, rhs: tuple[Q, ...]) -> tuple[Q, ...]:
    """Return the deterministic solution with every free variable set to zero."""

    if len(rhs) != matrix.rows:
        raise ValueError("linear-system right side has the wrong dimension")
    work = [list(matrix.entries[row]) + [rhs[row]] for row in range(matrix.rows)]
    pivot_columns: list[int] = []
    pivot_row = 0
    for col in range(matrix.cols):
        pivot = next(
            (row for row in range(pivot_row, matrix.rows) if work[row][col] != 0),
            None,
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        pivot_value = work[pivot_row][col]
        work[pivot_row] = [value / pivot_value for value in work[pivot_row]]
        for row in range(matrix.rows):
            if row == pivot_row or work[row][col] == 0:
                continue
            factor = work[row][col]
            work[row] = [
                work[row][index] - factor * work[pivot_row][index]
                for index in range(matrix.cols + 1)
            ]
        pivot_columns.append(col)
        pivot_row += 1
        if pivot_row == matrix.rows:
            break
    if any(
        all(work[row][col] == 0 for col in range(matrix.cols))
        and work[row][-1] != 0
        for row in range(matrix.rows)
    ):
        raise ValueError("linear system is inconsistent")
    solution = [Q(0) for _ in range(matrix.cols)]
    for row, pivot_col in enumerate(pivot_columns):
        solution[pivot_col] = work[row][-1]
    return tuple(solution)


@dataclass(frozen=True)
class H1MapMatrix:
    coarse_representatives: Matrix
    fine_representatives: Matrix
    induced_map: Matrix


def induced_h1_map_matrix(
    coarse_d0: Matrix,
    coarse_d1: Matrix,
    fine_d0: Matrix,
    fine_d1: Matrix,
    pullback1: Matrix,
) -> H1MapMatrix:
    coarse_representatives = quotient_h1_representatives(coarse_d0, coarse_d1)
    fine_representatives = quotient_h1_representatives(fine_d0, fine_d1)
    mapped = pullback1 @ coarse_representatives
    fine_span = Matrix.hstack(fine_d0, fine_representatives)
    data = [
        [Q(0) for _ in range(coarse_representatives.cols)]
        for _ in range(fine_representatives.cols)
    ]
    for column in range(mapped.cols):
        solution = solve_linear_system(
            fine_span,
            tuple(mapped.entries[row][column] for row in range(mapped.rows)),
        )
        quotient_coordinates = solution[fine_d0.cols :]
        for row, value in enumerate(quotient_coordinates):
            data[row][column] = value
    return H1MapMatrix(
        coarse_representatives=coarse_representatives,
        fine_representatives=fine_representatives,
        induced_map=Matrix.from_mutable(data, cols=coarse_representatives.cols),
    )


LawValue = int | bool
CoordinateBasis = tuple[tuple[int, LawValue], ...]


@dataclass(frozen=True)
class SingletonLawFamily:
    """One actual finite law, with source evaluation and both adequate descents."""

    name: str
    value_type: str
    source_evaluation: tuple[LawValue, ...]
    coarse_descend: tuple[LawValue, ...]
    fine_descend: tuple[LawValue, ...]
    law_type: str = "PUnit"
    law_carrier: tuple[str, ...] = ("unit",)

    def assertions(self, comparison: "UniformComparison") -> dict[str, bool]:
        return {
            "law_carrier_is_singleton": len(self.law_carrier) == 1,
            "source_is_fine_target": len(self.source_evaluation)
            == comparison.fine_target_count,
            "fine_descend_target_count": len(self.fine_descend)
            == comparison.fine_target_count,
            "coarse_descend_target_count": len(self.coarse_descend)
            == comparison.coarse_target_count,
            "fine_read_identity_adequate": self.source_evaluation
            == self.fine_descend,
            "coarse_read_pi_adequate": len(self.coarse_descend)
            == comparison.coarse_target_count
            and len(self.source_evaluation) == comparison.fine_target_count
            and all(
                self.coarse_descend[comparison.factor_pi[source]]
                == self.source_evaluation[source]
                for source in range(comparison.fine_target_count)
            ),
            "descents_commute_with_pi": len(self.fine_descend)
            == comparison.fine_target_count
            and len(self.coarse_descend) == comparison.coarse_target_count
            and all(
                self.fine_descend[target]
                == self.coarse_descend[comparison.factor_pi[target]]
                for target in range(comparison.fine_target_count)
            ),
        }

    def validate(self, comparison: "UniformComparison") -> None:
        assertions = self.assertions(comparison)
        if not all(assertions.values()):
            failed = [name for name, value in assertions.items() if not value]
            raise ValueError(f"invalid singleton law family: {failed}")

    def is_nonconstant(self) -> bool:
        return len(set(self.source_evaluation)) > 1


def block_diagonal(matrices: Sequence[Matrix]) -> Matrix:
    rows = sum(matrix.rows for matrix in matrices)
    cols = sum(matrix.cols for matrix in matrices)
    data = [[Q(0) for _ in range(cols)] for _ in range(rows)]
    row_offset = 0
    col_offset = 0
    for matrix in matrices:
        for row in range(matrix.rows):
            for col in range(matrix.cols):
                data[row_offset + row][col_offset + col] = matrix.entries[row][col]
        row_offset += matrix.rows
        col_offset += matrix.cols
    return Matrix.from_mutable(data, cols=cols)


def submatrix(
    matrix: Matrix,
    rows: Sequence[int],
    cols: Sequence[int],
) -> Matrix:
    return Matrix.from_mutable(
        [[matrix.entries[row][col] for col in cols] for row in rows],
        cols=len(cols),
    )


@dataclass(frozen=True)
class LawCoordinateComplex:
    """The actual singleton-law K0 coordinate bases and generated K1 matrices."""

    chart_basis: CoordinateBasis
    edge_basis: CoordinateBasis
    face_basis: CoordinateBasis
    d0: Matrix
    d1: Matrix

    def basis(self, dimension: int) -> CoordinateBasis:
        if dimension == 0:
            return self.chart_basis
        if dimension == 1:
            return self.edge_basis
        if dimension == 2:
            return self.face_basis
        raise ValueError("only dimensions zero through two are supported")


@dataclass(frozen=True)
class LawGeneratedComparison:
    """A global law-generated comparison, independent of coordinate subnerves."""

    values: tuple[LawValue, ...]
    coarse: LawCoordinateComplex
    fine: LawCoordinateComplex
    pullback0: Matrix
    pullback1: Matrix
    pullback2: Matrix

    def pullback(self, dimension: int) -> Matrix:
        if dimension == 0:
            return self.pullback0
        if dimension == 1:
            return self.pullback1
        if dimension == 2:
            return self.pullback2
        raise ValueError("only dimensions zero through two are supported")

    def analysis(self) -> H1Analysis:
        return analyze_complex_map(
            coarse_d0=self.coarse.d0,
            coarse_d1=self.coarse.d1,
            fine_d0=self.fine.d0,
            fine_d1=self.fine.d1,
            pullback0=self.pullback0,
            pullback1=self.pullback1,
            pullback2=self.pullback2,
        )

    def h1_map_matrix(self) -> H1MapMatrix:
        return induced_h1_map_matrix(
            self.coarse.d0,
            self.coarse.d1,
            self.fine.d0,
            self.fine.d1,
            self.pullback1,
        )


def cell_supports_by_dimension(
    nerve: Nerve,
    chart_supports: tuple[frozenset[int], ...],
    dimension: int,
) -> tuple[frozenset[int], ...]:
    edge_supports, face_supports = derived_cell_supports(nerve, chart_supports)
    if dimension == 0:
        return chart_supports
    if dimension == 1:
        return edge_supports
    if dimension == 2:
        return face_supports
    raise ValueError("only dimensions zero through two are supported")


def generated_value_order(descend: tuple[LawValue, ...]) -> tuple[LawValue, ...]:
    values: list[LawValue] = []
    for value in descend:
        if value not in values:
            values.append(value)
    return tuple(values)


def generated_coordinate_basis(
    supports: tuple[frozenset[int], ...],
    descend: tuple[LawValue, ...],
    values: tuple[LawValue, ...],
) -> CoordinateBasis:
    """K0 deduplicates targets with the same (cell, law, descend value)."""

    return tuple(
        (cell, value)
        for value in values
        for cell, support in enumerate(supports)
        if any(descend[target] == value for target in support)
    )


def build_law_generated_complex(
    nerve: Nerve,
    chart_supports: tuple[frozenset[int], ...],
    descend: tuple[LawValue, ...],
    values: tuple[LawValue, ...],
) -> LawCoordinateComplex:
    """Construct global K0/K1 coordinates directly from support and descend."""

    bases = tuple(
        generated_coordinate_basis(
            cell_supports_by_dimension(nerve, chart_supports, dimension),
            descend,
            values,
        )
        for dimension in range(3)
    )
    chart_index = {coordinate: index for index, coordinate in enumerate(bases[0])}
    edge_index = {coordinate: index for index, coordinate in enumerate(bases[1])}

    d0_data = [[Q(0) for _ in bases[0]] for _ in bases[1]]
    for row, (edge, value) in enumerate(bases[1]):
        left, right = nerve.edges[edge]
        d0_data[row][chart_index[(left, value)]] -= 1
        d0_data[row][chart_index[(right, value)]] += 1

    d1_data = [[Q(0) for _ in bases[1]] for _ in bases[2]]
    for row, (face, value) in enumerate(bases[2]):
        edge0, edge1, edge2 = nerve.faces[face]
        d1_data[row][edge_index[(edge0, value)]] += 1
        d1_data[row][edge_index[(edge1, value)]] -= 1
        d1_data[row][edge_index[(edge2, value)]] += 1

    complex_ = LawCoordinateComplex(
        chart_basis=bases[0],
        edge_basis=bases[1],
        face_basis=bases[2],
        d0=Matrix.from_mutable(d0_data, cols=len(bases[0])),
        d1=Matrix.from_mutable(d1_data, cols=len(bases[1])),
    )
    if not (complex_.d1 @ complex_.d0).is_zero():
        raise AssertionError("law-generated K1 incidence failed d1 * d0 = 0")
    return complex_


def generated_partial_pullback(
    coarse_basis: CoordinateBasis,
    fine_basis: CoordinateBasis,
    cell_map: Sequence[int | None],
) -> Matrix:
    coarse_index = {
        coordinate: index for index, coordinate in enumerate(coarse_basis)
    }
    data = [[Q(0) for _ in coarse_basis] for _ in fine_basis]
    for row, (fine_cell, value) in enumerate(fine_basis):
        coarse_cell = cell_map[fine_cell]
        if coarse_cell is None:
            continue
        coordinate = (coarse_cell, value)
        if coordinate not in coarse_index:
            raise AssertionError("generated fine coordinate lost its coarse image")
        data[row][coarse_index[coordinate]] = Q(1)
    return Matrix.from_mutable(data, cols=len(coarse_basis))


def build_law_generated_comparison(
    comparison: "UniformComparison",
    law_family: SingletonLawFamily,
) -> LawGeneratedComparison:
    """Build the actual global singleton-law map without A-subnerve calls."""

    law_family.validate(comparison)
    values = generated_value_order(law_family.fine_descend)
    coarse = build_law_generated_complex(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
        law_family.coarse_descend,
        values,
    )
    fine = build_law_generated_complex(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
        law_family.fine_descend,
        values,
    )
    generated = LawGeneratedComparison(
        values=values,
        coarse=coarse,
        fine=fine,
        pullback0=generated_partial_pullback(
            coarse.chart_basis,
            fine.chart_basis,
            comparison.morphism.vertex_map,
        ),
        pullback1=generated_partial_pullback(
            coarse.edge_basis,
            fine.edge_basis,
            comparison.morphism.edge_map,
        ),
        pullback2=generated_partial_pullback(
            coarse.face_basis,
            fine.face_basis,
            comparison.morphism.face_map,
        ),
    )
    generated.analysis()
    return generated


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
        chart_support_compatible = all(
            {
                self.factor_pi[target]
                for target in self.fine_chart_supports[fine_chart]
            }
            <= self.coarse_chart_supports[mapped_chart]
            for fine_chart, mapped_chart in enumerate(self.morphism.vertex_map)
        )
        coarse_derived = derived_cell_supports(
            self.morphism.coarse,
            self.coarse_chart_supports,
        )
        fine_derived = derived_cell_supports(
            self.morphism.fine,
            self.fine_chart_supports,
        )
        k1_supports_derived_by_intersection = (
            self.coarse_edge_supports == coarse_derived[0]
            and self.coarse_face_supports == coarse_derived[1]
            and self.fine_edge_supports == fine_derived[0]
            and self.fine_face_supports == fine_derived[1]
        )
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
            "chartSupport_compatible": chart_support_compatible,
            "K1_supports_derived_by_intersection": (
                k1_supports_derived_by_intersection
            ),
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


def build_value_block_direct_sum(
    comparison: UniformComparison,
    coarse_descend: tuple[LawValue, ...],
    values: tuple[LawValue, ...],
) -> LawGeneratedComparison:
    """Independently assemble the value-block A-subnerve direct sum."""

    subcomparisons = tuple(
        comparison.coordinate_subcomparison(
            frozenset(
                target
                for target, target_value in enumerate(coarse_descend)
                if target_value == value
            )
        )
        for value in values
    )
    # The explicit comprehension below is value-major, then ascending original cell.
    coarse_basis_by_dimension = tuple(
        tuple(
            (cell, value)
            for value, subcomparison in zip(values, subcomparisons, strict=True)
            for cell in (
                subcomparison.coarse.vertices,
                subcomparison.coarse.edges,
                subcomparison.coarse.faces,
            )[dimension]
        )
        for dimension in range(3)
    )
    fine_basis_by_dimension = tuple(
        tuple(
            (cell, value)
            for value, subcomparison in zip(values, subcomparisons, strict=True)
            for cell in (
                subcomparison.fine.vertices,
                subcomparison.fine.edges,
                subcomparison.fine.faces,
            )[dimension]
        )
        for dimension in range(3)
    )
    coarse = LawCoordinateComplex(
        chart_basis=coarse_basis_by_dimension[0],
        edge_basis=coarse_basis_by_dimension[1],
        face_basis=coarse_basis_by_dimension[2],
        d0=block_diagonal(
            tuple(subcomparison.morphism.coarse.d0() for subcomparison in subcomparisons)
        ),
        d1=block_diagonal(
            tuple(subcomparison.morphism.coarse.d1() for subcomparison in subcomparisons)
        ),
    )
    fine = LawCoordinateComplex(
        chart_basis=fine_basis_by_dimension[0],
        edge_basis=fine_basis_by_dimension[1],
        face_basis=fine_basis_by_dimension[2],
        d0=block_diagonal(
            tuple(subcomparison.morphism.fine.d0() for subcomparison in subcomparisons)
        ),
        d1=block_diagonal(
            tuple(subcomparison.morphism.fine.d1() for subcomparison in subcomparisons)
        ),
    )
    result = LawGeneratedComparison(
        values=values,
        coarse=coarse,
        fine=fine,
        pullback0=block_diagonal(
            tuple(subcomparison.morphism.cell_pullback(0) for subcomparison in subcomparisons)
        ),
        pullback1=block_diagonal(
            tuple(subcomparison.morphism.cell_pullback(1) for subcomparison in subcomparisons)
        ),
        pullback2=block_diagonal(
            tuple(subcomparison.morphism.cell_pullback(2) for subcomparison in subcomparisons)
        ),
    )
    result.analysis()
    return result


def extract_generated_value_block(
    generated: LawGeneratedComparison,
    value: LawValue,
) -> LawGeneratedComparison:
    coarse_indices = tuple(
        tuple(
            index
            for index, (_, coordinate_value) in enumerate(
                generated.coarse.basis(dimension)
            )
            if coordinate_value == value
        )
        for dimension in range(3)
    )
    fine_indices = tuple(
        tuple(
            index
            for index, (_, coordinate_value) in enumerate(
                generated.fine.basis(dimension)
            )
            if coordinate_value == value
        )
        for dimension in range(3)
    )
    coarse = LawCoordinateComplex(
        chart_basis=tuple(generated.coarse.chart_basis[index] for index in coarse_indices[0]),
        edge_basis=tuple(generated.coarse.edge_basis[index] for index in coarse_indices[1]),
        face_basis=tuple(generated.coarse.face_basis[index] for index in coarse_indices[2]),
        d0=submatrix(generated.coarse.d0, coarse_indices[1], coarse_indices[0]),
        d1=submatrix(generated.coarse.d1, coarse_indices[2], coarse_indices[1]),
    )
    fine = LawCoordinateComplex(
        chart_basis=tuple(generated.fine.chart_basis[index] for index in fine_indices[0]),
        edge_basis=tuple(generated.fine.edge_basis[index] for index in fine_indices[1]),
        face_basis=tuple(generated.fine.face_basis[index] for index in fine_indices[2]),
        d0=submatrix(generated.fine.d0, fine_indices[1], fine_indices[0]),
        d1=submatrix(generated.fine.d1, fine_indices[2], fine_indices[1]),
    )
    result = LawGeneratedComparison(
        values=(value,),
        coarse=coarse,
        fine=fine,
        pullback0=submatrix(
            generated.pullback0,
            fine_indices[0],
            coarse_indices[0],
        ),
        pullback1=submatrix(
            generated.pullback1,
            fine_indices[1],
            coarse_indices[1],
        ),
        pullback2=submatrix(
            generated.pullback2,
            fine_indices[2],
            coarse_indices[2],
        ),
    )
    result.analysis()
    return result


def exact_law_comparison_assertions(
    generated: LawGeneratedComparison,
    block_sum: LawGeneratedComparison,
) -> dict[str, bool]:
    return {
        "value_order": generated.values == block_sum.values,
        "coarse_chart_basis": generated.coarse.chart_basis
        == block_sum.coarse.chart_basis,
        "coarse_edge_basis": generated.coarse.edge_basis == block_sum.coarse.edge_basis,
        "coarse_face_basis": generated.coarse.face_basis == block_sum.coarse.face_basis,
        "fine_chart_basis": generated.fine.chart_basis == block_sum.fine.chart_basis,
        "fine_edge_basis": generated.fine.edge_basis == block_sum.fine.edge_basis,
        "fine_face_basis": generated.fine.face_basis == block_sum.fine.face_basis,
        "coarse_d0": generated.coarse.d0 == block_sum.coarse.d0,
        "coarse_d1": generated.coarse.d1 == block_sum.coarse.d1,
        "fine_d0": generated.fine.d0 == block_sum.fine.d0,
        "fine_d1": generated.fine.d1 == block_sum.fine.d1,
        "pullback0": generated.pullback0 == block_sum.pullback0,
        "pullback1": generated.pullback1 == block_sum.pullback1,
        "pullback2": generated.pullback2 == block_sum.pullback2,
        "H1_analysis": generated.analysis() == block_sum.analysis(),
        "H1_coarse_representatives": (
            generated.h1_map_matrix().coarse_representatives
            == block_sum.h1_map_matrix().coarse_representatives
        ),
        "H1_fine_representatives": (
            generated.h1_map_matrix().fine_representatives
            == block_sum.h1_map_matrix().fine_representatives
        ),
        "H1_map_matrix": generated.h1_map_matrix().induced_map
        == block_sum.h1_map_matrix().induced_map,
    }


def rational_summary(value: Q) -> int | str:
    return value.numerator if value.denominator == 1 else str(value)


def matrix_summary(matrix: Matrix) -> dict[str, object]:
    return {
        "rows": matrix.rows,
        "cols": matrix.cols,
        "entries": [
            [rational_summary(value) for value in row] for row in matrix.entries
        ],
    }


def basis_summary(basis: CoordinateBasis) -> list[dict[str, object]]:
    return [{"cell": cell, "value": value} for cell, value in basis]


def law_complex_summary(complex_: LawCoordinateComplex) -> dict[str, object]:
    return {
        "basis": {
            "charts": basis_summary(complex_.chart_basis),
            "edges": basis_summary(complex_.edge_basis),
            "faces": basis_summary(complex_.face_basis),
        },
        "dimensions": {
            "charts": len(complex_.chart_basis),
            "edges": len(complex_.edge_basis),
            "faces": len(complex_.face_basis),
        },
        "d0": matrix_summary(complex_.d0),
        "d1": matrix_summary(complex_.d1),
    }


def law_comparison_summary(
    comparison: LawGeneratedComparison,
) -> dict[str, object]:
    h1_map = comparison.h1_map_matrix()
    return {
        "values": list(comparison.values),
        "coarse": law_complex_summary(comparison.coarse),
        "fine": law_complex_summary(comparison.fine),
        "pullback0": matrix_summary(comparison.pullback0),
        "pullback1": matrix_summary(comparison.pullback1),
        "pullback2": matrix_summary(comparison.pullback2),
        "h1": asdict(comparison.analysis()),
        "h1_map": {
            "coarse_representatives": matrix_summary(
                h1_map.coarse_representatives
            ),
            "fine_representatives": matrix_summary(h1_map.fine_representatives),
            "matrix": matrix_summary(h1_map.induced_map),
        },
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
        evaluation["calibration_pass"] = passed
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
        "calibration_pass": passed,
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


def canonical_firing_law_family() -> SingletonLawFamily:
    """The exact PUnit/Fin 2 law family fixed by the Lean firing witness."""

    return SingletonLawFamily(
        name="canonical_nonconstant_law",
        law_type="PUnit",
        law_carrier=("unit",),
        value_type="Fin 2",
        source_evaluation=(0, 0, 1),
        coarse_descend=(0, 1),
        fine_descend=(0, 0, 1),
    )


def first_duplicate_image_witness(
    mapping: Sequence[int],
) -> dict[str, object] | None:
    """Return the first deterministic witness that a finite map is noninjective."""

    for left, right in combinations(range(len(mapping)), 2):
        if mapping[left] == mapping[right]:
            return {
                "domain_elements": [left, right],
                "common_image": mapping[left],
            }
    return None


def canonical_fixed_fixture_data(
    comparison: UniformComparison,
    law_family: SingletonLawFamily,
) -> dict[str, object]:
    """Expose every fixed array used by the canonical firing calibration."""

    return {
        "name": comparison.name,
        "target_counts": {
            "coarse": comparison.coarse_target_count,
            "fine": comparison.fine_target_count,
        },
        "factor_pi": list(comparison.factor_pi),
        "coarse": {
            "nerve": nerve_summary(comparison.morphism.coarse),
            "chart_supports": supports_summary(comparison.coarse_chart_supports),
            "edge_supports": supports_summary(comparison.coarse_edge_supports),
            "face_supports": supports_summary(comparison.coarse_face_supports),
        },
        "fine": {
            "nerve": nerve_summary(comparison.morphism.fine),
            "chart_supports": supports_summary(comparison.fine_chart_supports),
            "edge_supports": supports_summary(comparison.fine_edge_supports),
            "face_supports": supports_summary(comparison.fine_face_supports),
        },
        "morphism": {
            "chart_map_phi": list(comparison.morphism.vertex_map),
            "edge_map": list(comparison.morphism.edge_map),
            "face_map": list(comparison.morphism.face_map),
        },
        "law_family": {
            "name": law_family.name,
            "law_type": law_family.law_type,
            "law_carrier": list(law_family.law_carrier),
            "value_type": law_family.value_type,
            "source_evaluation": list(law_family.source_evaluation),
            "coarse_descend": list(law_family.coarse_descend),
            "fine_descend": list(law_family.fine_descend),
        },
    }


def canonical_fixed_fixture_assertions(
    comparison: UniformComparison,
    law_family: SingletonLawFamily,
) -> tuple[dict[str, object], dict[str, bool]]:
    """Fail closed unless the complete reviewed fixture is still byte-for-byte exact."""

    actual = canonical_fixed_fixture_data(comparison, law_family)
    expected = {
        "name": "ResolutionInvarianceFiringData",
        "target_counts": {"coarse": 2, "fine": 3},
        "factor_pi": [0, 0, 1],
        "coarse": {
            "nerve": {
                "vertices": 2,
                "edges": [[0, 1], [1, 0], [0, 0]],
                "faces": [[2, 2, 2]],
            },
            "chart_supports": [[0, 1], [0]],
            "edge_supports": [[0], [0], [0, 1]],
            "face_supports": [[0, 1]],
        },
        "fine": {
            "nerve": {
                "vertices": 3,
                "edges": [[0, 2], [2, 0], [0, 0], [0, 1], [1, 1]],
                "faces": [[2, 2, 2], [4, 4, 4]],
            },
            "chart_supports": [[0, 2], [0, 1], [0]],
            "edge_supports": [[0], [0], [0, 2], [0], [0, 1]],
            "face_supports": [[0, 2], [0, 1]],
        },
        "morphism": {
            "chart_map_phi": [0, 0, 1],
            "edge_map": [0, 1, 2, None, None],
            "face_map": [0, None],
        },
        "law_family": {
            "name": "canonical_nonconstant_law",
            "law_type": "PUnit",
            "law_carrier": ["unit"],
            "value_type": "Fin 2",
            "source_evaluation": [0, 0, 1],
            "coarse_descend": [0, 1],
            "fine_descend": [0, 0, 1],
        },
    }
    assertions = {
        "fixture_name": actual["name"] == expected["name"],
        "target_counts": actual["target_counts"] == expected["target_counts"],
        "factor_pi": actual["factor_pi"] == expected["factor_pi"],
        "coarse_nerve": actual["coarse"]["nerve"]
        == expected["coarse"]["nerve"],
        "coarse_chart_supports": actual["coarse"]["chart_supports"]
        == expected["coarse"]["chart_supports"],
        "coarse_edge_supports": actual["coarse"]["edge_supports"]
        == expected["coarse"]["edge_supports"],
        "coarse_face_supports": actual["coarse"]["face_supports"]
        == expected["coarse"]["face_supports"],
        "fine_nerve": actual["fine"]["nerve"] == expected["fine"]["nerve"],
        "fine_chart_supports": actual["fine"]["chart_supports"]
        == expected["fine"]["chart_supports"],
        "fine_edge_supports": actual["fine"]["edge_supports"]
        == expected["fine"]["edge_supports"],
        "fine_face_supports": actual["fine"]["face_supports"]
        == expected["fine"]["face_supports"],
        "chart_map_phi": actual["morphism"]["chart_map_phi"]
        == expected["morphism"]["chart_map_phi"],
        "edge_map": actual["morphism"]["edge_map"]
        == expected["morphism"]["edge_map"],
        "face_map": actual["morphism"]["face_map"]
        == expected["morphism"]["face_map"],
        "law_family_name": actual["law_family"]["name"]
        == expected["law_family"]["name"],
        "law_type_PUnit": actual["law_family"]["law_type"]
        == expected["law_family"]["law_type"],
        "law_carrier_unit_singleton": actual["law_family"]["law_carrier"]
        == expected["law_family"]["law_carrier"],
        "value_type_Fin_2": actual["law_family"]["value_type"]
        == expected["law_family"]["value_type"],
        "law_family_arrays": actual["law_family"] == expected["law_family"],
        "complete_fixed_fixture": actual == expected,
    }
    return actual, assertions


def canonical_nonvacuity_evidence(
    comparison: UniformComparison,
) -> tuple[dict[str, object], dict[str, bool]]:
    """Compute the distinct nonvacuity features of the firing fixture."""

    morphism = comparison.morphism
    pi_witness = first_duplicate_image_witness(comparison.factor_pi)
    phi_witness = first_duplicate_image_witness(morphism.vertex_map)
    map_properties = {
        "pi_fine_target_to_coarse_target": {
            "mapping": list(comparison.factor_pi),
            "surjective": set(comparison.factor_pi)
            == set(range(comparison.coarse_target_count)),
            "noninjective_witness": pi_witness,
        },
        "phi_fine_chart_to_coarse_chart": {
            "mapping": list(morphism.vertex_map),
            "surjective": set(morphism.vertex_map)
            == set(range(morphism.coarse.vertices)),
            "noninjective_witness": phi_witness,
        },
    }
    mapped_faces = [
        {
            "fine_face": fine_face,
            "coarse_face": coarse_face,
            "fine_boundary": list(morphism.fine.faces[fine_face]),
            "mapped_boundary": [
                morphism.edge_map[edge]
                for edge in morphism.fine.faces[fine_face]
            ],
            "coarse_boundary": list(morphism.coarse.faces[coarse_face]),
        }
        for fine_face, coarse_face in enumerate(morphism.face_map)
        if coarse_face is not None
    ]
    degenerate_edges = [
        {
            "fine_edge": fine_edge,
            "endpoints": list(morphism.fine.edges[fine_edge]),
            "mapped_endpoints": [
                morphism.vertex_map[endpoint]
                for endpoint in morphism.fine.edges[fine_edge]
            ],
            "support": sorted(comparison.fine_edge_supports[fine_edge]),
        }
        for fine_edge, coarse_edge in enumerate(morphism.edge_map)
        if coarse_edge is None
    ]
    degenerate_faces = [
        {
            "fine_face": fine_face,
            "boundary": list(morphism.fine.faces[fine_face]),
            "mapped_boundary": [
                morphism.edge_map[edge]
                for edge in morphism.fine.faces[fine_face]
            ],
            "support": sorted(comparison.fine_face_supports[fine_face]),
        }
        for fine_face, coarse_face in enumerate(morphism.face_map)
        if coarse_face is None
    ]
    one_label = comparison.coordinate_subcomparison(frozenset((1,)))
    one_label_signature = {
        "coarse_targets_A": sorted(one_label.coarse_targets),
        "fine_targets_pi_preimage_A": sorted(one_label.fine_targets),
        "coarse_original_cells": {
            "charts": list(one_label.coarse.vertices),
            "edges": list(one_label.coarse.edges),
            "faces": list(one_label.coarse.faces),
        },
        "fine_original_cells": {
            "charts": list(one_label.fine.vertices),
            "edges": list(one_label.fine.edges),
            "faces": list(one_label.fine.faces),
        },
        "coarse_incidence": nerve_summary(one_label.morphism.coarse),
        "fine_incidence": nerve_summary(one_label.morphism.fine),
        "restricted_maps": {
            "chart_map_phi": list(one_label.morphism.vertex_map),
            "edge_map": list(one_label.morphism.edge_map),
            "face_map": list(one_label.morphism.face_map),
        },
    }
    whole_coarse_cells = (
        tuple(range(morphism.coarse.vertices)),
        tuple(range(len(morphism.coarse.edges))),
        tuple(range(len(morphism.coarse.faces))),
    )
    whole_fine_cells = (
        tuple(range(morphism.fine.vertices)),
        tuple(range(len(morphism.fine.edges))),
        tuple(range(len(morphism.fine.faces))),
    )
    selected_coarse_cells = (
        one_label.coarse.vertices,
        one_label.coarse.edges,
        one_label.coarse.faces,
    )
    selected_fine_cells = (
        one_label.fine.vertices,
        one_label.fine.edges,
        one_label.fine.faces,
    )
    evidence = {
        "map_properties": map_properties,
        "mapped_faces": mapped_faces,
        "degenerate_edges": degenerate_edges,
        "degenerate_faces": degenerate_faces,
        "proper_one_label_subnerve": one_label_signature,
    }
    assertions = {
        "pi_surjective": map_properties[
            "pi_fine_target_to_coarse_target"
        ]["surjective"],
        "pi_separately_noninjective": pi_witness
        == {"domain_elements": [0, 1], "common_image": 0},
        "phi_surjective": map_properties[
            "phi_fine_chart_to_coarse_chart"
        ]["surjective"],
        "phi_separately_noninjective": phi_witness
        == {"domain_elements": [0, 1], "common_image": 0},
        "mapped_face_present": mapped_faces
        == [
            {
                "fine_face": 0,
                "coarse_face": 0,
                "fine_boundary": [2, 2, 2],
                "mapped_boundary": [2, 2, 2],
                "coarse_boundary": [2, 2, 2],
            }
        ],
        "degenerate_edges_present": degenerate_edges
        == [
            {
                "fine_edge": 3,
                "endpoints": [0, 1],
                "mapped_endpoints": [0, 0],
                "support": [0],
            },
            {
                "fine_edge": 4,
                "endpoints": [1, 1],
                "mapped_endpoints": [0, 0],
                "support": [0, 1],
            },
        ],
        "degenerate_face_present": degenerate_faces
        == [
            {
                "fine_face": 1,
                "boundary": [4, 4, 4],
                "mapped_boundary": [None, None, None],
                "support": [0, 1],
            }
        ],
        "one_label_subnerve_exact": one_label_signature
        == {
            "coarse_targets_A": [1],
            "fine_targets_pi_preimage_A": [2],
            "coarse_original_cells": {
                "charts": [0],
                "edges": [2],
                "faces": [0],
            },
            "fine_original_cells": {
                "charts": [0],
                "edges": [2],
                "faces": [0],
            },
            "coarse_incidence": {
                "vertices": 1,
                "edges": [[0, 0]],
                "faces": [[0, 0, 0]],
            },
            "fine_incidence": {
                "vertices": 1,
                "edges": [[0, 0]],
                "faces": [[0, 0, 0]],
            },
            "restricted_maps": {
                "chart_map_phi": [0],
                "edge_map": [0],
                "face_map": [0],
            },
        },
        "one_label_subnerve_is_proper_on_both_sides": (
            selected_coarse_cells != whole_coarse_cells
            and selected_fine_cells != whole_fine_cells
        ),
    }
    return evidence, assertions


def canonical_firing_class_evidence(
    generated: LawGeneratedComparison,
) -> tuple[dict[str, object], dict[str, bool]]:
    """Directly certify the concrete firing cocycle and its generated image."""

    coarse_firing = Matrix.from_mutable(
        [
            [Q(1 if cell == 0 else 0)]
            for cell, _value in generated.coarse.edge_basis
        ],
        cols=1,
    )
    fine_image = generated.pullback1 @ coarse_firing
    coarse_cycle_value = generated.coarse.d1 @ coarse_firing
    fine_cycle_value = generated.fine.d1 @ fine_image
    coarse_boundary_rank = generated.coarse.d0.rank()
    fine_boundary_rank = generated.fine.d0.rank()
    coarse_augmented_rank = Matrix.hstack(
        generated.coarse.d0,
        coarse_firing,
    ).rank()
    fine_augmented_rank = Matrix.hstack(
        generated.fine.d0,
        fine_image,
    ).rank()
    directed_period = Matrix.from_mutable(
        [
            [
                Q(1 if value == 0 and cell in (0, 1) else 0)
                for cell, value in generated.coarse.edge_basis
            ]
        ],
        cols=len(generated.coarse.edge_basis),
    )
    period_on_boundaries = directed_period @ generated.coarse.d0
    period_on_firing = directed_period @ coarse_firing
    h1_map = generated.h1_map_matrix()
    evidence = {
        "coarse_firing_rule": "one exactly on coarse edge cell 0",
        "coarse_firing_1_cochain": matrix_summary(coarse_firing),
        "coarse_coboundary_rank": coarse_boundary_rank,
        "coarse_coboundary_plus_firing_rank": coarse_augmented_rank,
        "coarse_cycle_value": matrix_summary(coarse_cycle_value),
        "directed_period_functional": matrix_summary(directed_period),
        "directed_period_on_coboundaries": matrix_summary(period_on_boundaries),
        "directed_period_on_firing": matrix_summary(period_on_firing),
        "generated_fine_image": matrix_summary(fine_image),
        "fine_coboundary_rank": fine_boundary_rank,
        "fine_coboundary_plus_image_rank": fine_augmented_rank,
        "fine_cycle_value": matrix_summary(fine_cycle_value),
        "induced_H1_map": matrix_summary(h1_map.induced_map),
    }
    assertions = {
        "coarse_firing_is_fixed_nonzero_cochain": coarse_firing
        == Matrix.from_mutable(((1,), (0,), (0,), (0,))),
        "coarse_firing_is_cycle": coarse_cycle_value.is_zero(),
        "directed_period_annihilates_all_coboundaries": (
            period_on_boundaries.is_zero()
        ),
        "coarse_firing_has_nonzero_directed_period": period_on_firing
        == Matrix.from_mutable(((1,),)),
        "coarse_firing_is_nonboundary": coarse_augmented_rank
        > coarse_boundary_rank,
        "generated_fine_image_is_fixed": fine_image
        == Matrix.from_mutable(((1,), (0,), (0,), (0,), (0,), (0,))),
        "generated_fine_image_is_cycle": fine_cycle_value.is_zero(),
        "generated_fine_image_is_nonboundary": fine_augmented_rank
        > fine_boundary_rank,
        "firing_representatives_are_the_computed_H1_bases": (
            coarse_firing == h1_map.coarse_representatives
            and fine_image == h1_map.fine_representatives
        ),
        "firing_class_maps_nontrivially": h1_map.induced_map
        == Matrix.from_mutable(((1,),)),
    }
    return evidence, assertions


def canonical_firing_report() -> dict[str, object]:
    comparison = canonical_firing_fixture()
    evaluation = comparison_evaluation(comparison)
    block_by_targets = {
        tuple(block["coarse_targets_A"]): block for block in evaluation["blocks"]
    }
    zero = block_by_targets[(0,)]["h1"]
    one = block_by_targets[(1,)]["h1"]
    law_family = canonical_firing_law_family()
    generated = build_law_generated_comparison(
        comparison,
        law_family,
    )
    block_sum = build_value_block_direct_sum(
        comparison,
        law_family.coarse_descend,
        generated.values,
    )
    exact_assertions = exact_law_comparison_assertions(generated, block_sum)
    fixed_fixture, fixed_fixture_assertions = canonical_fixed_fixture_assertions(
        comparison,
        law_family,
    )
    nonvacuity, nonvacuity_assertions = canonical_nonvacuity_evidence(comparison)
    firing_class, firing_class_assertions = canonical_firing_class_evidence(
        generated
    )
    global_analysis = generated.analysis()
    expected_zero = {
        "coarse_h1_dimension": 1,
        "fine_h1_dimension": 1,
        "comparison_rank": 1,
        "injective": True,
        "surjective": True,
        "isomorphism": True,
    }
    expected_one = {
        "coarse_h1_dimension": 0,
        "fine_h1_dimension": 0,
        "comparison_rank": 0,
        "injective": True,
        "surjective": True,
        "isomorphism": True,
    }
    computed_assertions = {
        "singleton_nonconstant_law": law_family.is_nonconstant()
        and generated.values == (0, 1),
        "actual_law_family_fields": all(
            law_family.assertions(comparison).values()
        ),
        "coarse_K0_K1_dimensions": (
            len(generated.coarse.chart_basis),
            len(generated.coarse.edge_basis),
            len(generated.coarse.face_basis),
        )
        == (3, 4, 2),
        "fine_K0_K1_dimensions": (
            len(generated.fine.chart_basis),
            len(generated.fine.edge_basis),
            len(generated.fine.face_basis),
        )
        == (4, 6, 3),
        "global_H1": global_analysis == H1Analysis(1, 1, 1, True, True, True),
        "zero_block_H1": zero == expected_zero,
        "one_block_H1": one == expected_one,
        "uniform_all_nonempty_A": evaluation["uniform"],
        "all_C0_C6": all(evaluation["conditions"]["aggregate"].values()),
        "global_and_block_H1_equal": generated.analysis() == block_sum.analysis(),
    }
    block_reduction_pass = all(exact_assertions.values())
    canonical_oracle_pass = all(
        (
            block_reduction_pass,
            all(fixed_fixture_assertions.values()),
            all(nonvacuity_assertions.values()),
            all(firing_class_assertions.values()),
            all(computed_assertions.values()),
        )
    )
    if not canonical_oracle_pass:
        raise AssertionError("canonical firing oracle mismatch")
    return {
        **evaluation,
        "actual_law_blocks": {
            "value_zero": block_by_targets[(0,)],
            "value_one": block_by_targets[(1,)],
        },
        "singleton_nonconstant_law_family": {
            "Law": law_family.law_type,
            "Law_carrier": list(law_family.law_carrier),
            "Value": law_family.value_type,
            "coarse_descend": list(law_family.coarse_descend),
            "fine_descend": list(law_family.fine_descend),
            "source_evaluation": list(law_family.source_evaluation),
            "assertions": law_family.assertions(comparison),
        },
        "law_generated_global": law_comparison_summary(generated),
        "value_block_A_subnerve_direct_sum": law_comparison_summary(block_sum),
        "exact_global_block_matrix_equality": exact_assertions,
        "canonical_fixed_fixture": fixed_fixture,
        "canonical_fixed_fixture_assertions": fixed_fixture_assertions,
        "canonical_nonvacuity_evidence": nonvacuity,
        "canonical_nonvacuity_assertions": nonvacuity_assertions,
        "canonical_firing_class_evidence": firing_class,
        "canonical_firing_class_assertions": firing_class_assertions,
        "computed_oracle_assertions": computed_assertions,
        "global_supported_direct_sum": asdict(global_analysis),
        "block_reduction_pass": block_reduction_pass,
        "canonical_oracle_pass": canonical_oracle_pass,
    }


def subcomparison_value_block(
    subcomparison: CoordinateSubcomparison,
    value: LawValue,
) -> LawGeneratedComparison:
    coarse = LawCoordinateComplex(
        chart_basis=tuple((cell, value) for cell in subcomparison.coarse.vertices),
        edge_basis=tuple((cell, value) for cell in subcomparison.coarse.edges),
        face_basis=tuple((cell, value) for cell in subcomparison.coarse.faces),
        d0=subcomparison.morphism.coarse.d0(),
        d1=subcomparison.morphism.coarse.d1(),
    )
    fine = LawCoordinateComplex(
        chart_basis=tuple((cell, value) for cell in subcomparison.fine.vertices),
        edge_basis=tuple((cell, value) for cell in subcomparison.fine.edges),
        face_basis=tuple((cell, value) for cell in subcomparison.fine.faces),
        d0=subcomparison.morphism.fine.d0(),
        d1=subcomparison.morphism.fine.d1(),
    )
    result = LawGeneratedComparison(
        values=(value,),
        coarse=coarse,
        fine=fine,
        pullback0=subcomparison.morphism.cell_pullback(0),
        pullback1=subcomparison.morphism.cell_pullback(1),
        pullback2=subcomparison.morphism.cell_pullback(2),
    )
    result.analysis()
    return result


def incidence_signature_from_generated_basis(
    nerve: Nerve,
    complex_: LawCoordinateComplex,
    value: LawValue,
) -> dict[str, object]:
    vertices = tuple(cell for cell, basis_value in complex_.chart_basis if basis_value == value)
    edges = tuple(cell for cell, basis_value in complex_.edge_basis if basis_value == value)
    faces = tuple(cell for cell, basis_value in complex_.face_basis if basis_value == value)
    vertex_index = {cell: index for index, cell in enumerate(vertices)}
    edge_index = {cell: index for index, cell in enumerate(edges)}
    restricted = Nerve(
        len(vertices),
        tuple(
            (vertex_index[nerve.edges[edge][0]], vertex_index[nerve.edges[edge][1]])
            for edge in edges
        ),
        tuple(
            tuple(edge_index[edge] for edge in nerve.faces[face])
            for face in faces
        ),
    )
    return {
        "original_cells": {
            "charts": list(vertices),
            "edges": list(edges),
            "faces": list(faces),
        },
        "incidence": nerve_summary(restricted),
    }


def partial_map_signature_from_generated_basis(
    comparison: UniformComparison,
    generated_block: LawGeneratedComparison,
    value: LawValue,
) -> dict[str, list[dict[str, int | None]]]:
    mappings: tuple[Sequence[int | None], ...] = (
        comparison.morphism.vertex_map,
        comparison.morphism.edge_map,
        comparison.morphism.face_map,
    )
    result = {}
    for dimension, label in enumerate(("charts", "edges", "faces")):
        result[label] = [
            {"fine_cell": cell, "coarse_cell": mappings[dimension][cell]}
            for cell, basis_value in generated_block.fine.basis(dimension)
            if basis_value == value
        ]
    return result


def value_coordinate_dedup_stats(
    comparison: UniformComparison,
    generated_block: LawGeneratedComparison,
    coarse_descend: tuple[LawValue, ...],
    fine_descend: tuple[LawValue, ...],
    value: LawValue,
) -> dict[str, object]:
    result: dict[str, object] = {}
    for side, nerve, chart_supports, descend, complex_ in (
        (
            "coarse",
            comparison.morphism.coarse,
            comparison.coarse_chart_supports,
            coarse_descend,
            generated_block.coarse,
        ),
        (
            "fine",
            comparison.morphism.fine,
            comparison.fine_chart_supports,
            fine_descend,
            generated_block.fine,
        ),
    ):
        side_stats = {}
        for dimension, label in enumerate(("charts", "edges", "faces")):
            supports = cell_supports_by_dimension(nerve, chart_supports, dimension)
            raw_target_occurrences = sum(
                sum(descend[target] == value for target in support)
                for support in supports
            )
            coordinate_count = len(complex_.basis(dimension))
            side_stats[label] = {
                "raw_supported_target_occurrences": raw_target_occurrences,
                "deduplicated_cell_law_value_coordinates": coordinate_count,
                "deduplicated_occurrences": raw_target_occurrences - coordinate_count,
            }
        result[side] = side_stats
    return result


def indicator_factor_report(
    name: str,
    comparison: UniformComparison,
) -> dict[str, object]:
    """Realize every A and compare its actual True block cell-for-cell."""

    factor_pi = comparison.factor_pi
    coarse_target_count = comparison.coarse_target_count
    fine_target_count = comparison.fine_target_count
    source = tuple(range(fine_target_count))
    fine_read = tuple(range(fine_target_count))
    coarse_read = tuple(factor_pi[target] for target in fine_read)
    unit_law_carrier = ("unit",)
    bool_values = (False, True)
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
        law_family = SingletonLawFamily(
            name=f"indicator_{name}_A_{'_'.join(map(str, sorted(targets)))}",
            value_type="Bool",
            source_evaluation=law_evaluation,
            coarse_descend=coarse_descent,
            fine_descend=fine_descent,
        )
        generated = build_law_generated_comparison(
            comparison,
            law_family,
        )
        true_block = extract_generated_value_block(generated, True)
        subcomparison = comparison.coordinate_subcomparison(targets)
        expected_true_block = subcomparison_value_block(subcomparison, True)
        block_assertions = exact_law_comparison_assertions(
            true_block,
            expected_true_block,
        )
        coarse_signature = incidence_signature_from_generated_basis(
            comparison.morphism.coarse,
            true_block.coarse,
            True,
        )
        fine_signature = incidence_signature_from_generated_basis(
            comparison.morphism.fine,
            true_block.fine,
            True,
        )
        partial_map_signature = partial_map_signature_from_generated_basis(
            comparison,
            true_block,
            True,
        )
        expected_partial_map_signature = {
            label: [
                {
                    "fine_cell": cell,
                    "coarse_cell": mappings[cell],
                }
                for cell in selected_cells
            ]
            for label, mappings, selected_cells in (
                (
                    "charts",
                    comparison.morphism.vertex_map,
                    subcomparison.fine.vertices,
                ),
                (
                    "edges",
                    comparison.morphism.edge_map,
                    subcomparison.fine.edges,
                ),
                (
                    "faces",
                    comparison.morphism.face_map,
                    subcomparison.fine.faces,
                ),
            )
        }
        actual_signatures = {
            "coarse": coarse_signature,
            "fine": fine_signature,
            "partial_map_original_cells": partial_map_signature,
        }
        expected_signatures = {
            "coarse": {
                "original_cells": {
                    "charts": list(subcomparison.coarse.vertices),
                    "edges": list(subcomparison.coarse.edges),
                    "faces": list(subcomparison.coarse.faces),
                },
                "incidence": nerve_summary(subcomparison.morphism.coarse),
            },
            "fine": {
                "original_cells": {
                    "charts": list(subcomparison.fine.vertices),
                    "edges": list(subcomparison.fine.edges),
                    "faces": list(subcomparison.fine.faces),
                },
                "incidence": nerve_summary(subcomparison.morphism.fine),
            },
            "partial_map_original_cells": expected_partial_map_signature,
        }
        signature_assertions = {
            **block_assertions,
            "coarse_original_cell_signature": coarse_signature["original_cells"]
            == {
                "charts": list(subcomparison.coarse.vertices),
                "edges": list(subcomparison.coarse.edges),
                "faces": list(subcomparison.coarse.faces),
            },
            "fine_original_cell_signature": fine_signature["original_cells"]
            == {
                "charts": list(subcomparison.fine.vertices),
                "edges": list(subcomparison.fine.edges),
                "faces": list(subcomparison.fine.faces),
            },
            "coarse_incidence": coarse_signature["incidence"]
            == nerve_summary(subcomparison.morphism.coarse),
            "fine_incidence": fine_signature["incidence"]
            == nerve_summary(subcomparison.morphism.fine),
            "partial_map_original_cell_signature": partial_map_signature
            == expected_partial_map_signature,
            "complete_original_cell_incidence_partial_map_signature": (
                actual_signatures == expected_signatures
            ),
        }
        assertions = {
            "fine_read_identity_surjective": (
                len(fine_read) == fine_target_count
                and all(fine_read[source_cell] == source_cell for source_cell in source)
                and set(fine_read) == set(range(fine_target_count))
            ),
            "coarse_read_pi_surjective": set(factor_pi)
            == set(range(coarse_target_count)),
            "coarse_read_factors_through_fine": all(
                coarse_read[source_cell] == factor_pi[fine_read[source_cell]]
                for source_cell in source
            ),
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
            "unit_law_family_fields_finite": (
                law_family.law_type == "PUnit"
                and law_family.law_carrier == unit_law_carrier
                and law_family.value_type == "Bool"
                and len(law_family.law_carrier) == len(set(unit_law_carrier)) == 1
                and len(law_family.source_evaluation) == len(source)
            ),
            "actual_singleton_law_family_fields": all(
                law_family.assertions(comparison).values()
            ),
            "bool_has_two_distinct_values": (
                len(set(bool_values)) == 2
                and bool_values[0] != bool_values[1]
            ),
            "true_coordinate_block_matches_A_subnerve_all_cells": all(
                signature_assertions.values()
            ),
        }
        if not all(assertions.values()):
            raise AssertionError(f"indicator realization failed for {name} A={targets}")
        dedup = value_coordinate_dedup_stats(
            comparison,
            true_block,
            coarse_descent,
            fine_descent,
            True,
        )
        cases.append(
            {
                "coarse_targets_A": sorted(targets),
                "fine_targets_pi_preimage_A": sorted(expected_fine),
                "coarse_bool_descent": list(coarse_descent),
                "fine_bool_descent": list(fine_descent),
                "law_evaluation_on_source_eq_fine_target": list(law_evaluation),
                "actual_true_coordinate_block": law_comparison_summary(true_block),
                "A_subnerve_constant_Q_block": law_comparison_summary(
                    expected_true_block
                ),
                "actual_true_block_signatures": actual_signatures,
                "A_subnerve_signatures": expected_signatures,
                "cell_incidence_partial_map_assertions": signature_assertions,
                "coordinate_dedup": dedup,
                "assertions": assertions,
            }
        )
    dedup_fired_by_dimension = {
        label: any(
            case["coordinate_dedup"][side][label]["deduplicated_occurrences"] > 0
            for case in cases
            for side in ("coarse", "fine")
        )
        for label in ("charts", "edges", "faces")
    }
    all_pass = (
        all(all(case["assertions"].values()) for case in cases)
        and all(
            all(case["cell_incidence_partial_map_assertions"].values())
            for case in cases
        )
        and all(dedup_fired_by_dimension.values())
    )
    if not all_pass:
        raise AssertionError(f"indicator cell-signature gate failed for {name}")
    return {
        "name": name,
        "source_count": len(source),
        "fine_read": list(fine_read),
        "coarse_read": list(coarse_read),
        "factor_pi": list(factor_pi),
        "law_type": law_family.law_type,
        "law_type_cardinality": len(set(unit_law_carrier)),
        "value_type": "Bool",
        "value_type_cardinality": len(set(bool_values)),
        "nonempty_subset_count": len(cases),
        "cases": cases,
        "dedup_fired_by_dimension": dedup_fired_by_dimension,
        "all_pass": all_pass,
    }


def indicator_realizability_report() -> dict[str, object]:
    factors = (
        indicator_factor_report("Fin3_to_Fin2", canonical_firing_fixture()),
        indicator_factor_report("Fin4_to_Fin3", legacy_positive_fixture()),
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
                "law_generated_global": firing["law_generated_global"],
                "value_block_A_subnerve_direct_sum": firing[
                    "value_block_A_subnerve_direct_sum"
                ],
                "exact_global_block_matrix_equality": firing[
                    "exact_global_block_matrix_equality"
                ],
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
