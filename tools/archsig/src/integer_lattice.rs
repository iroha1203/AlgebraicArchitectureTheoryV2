//! 有限生成自由アーベル群 `Z^n` の部分格子を、列 Hermite 正規形で決定する。
//!
//! 第X部 定義 10.1 は Smith normal form で `im(R_V)=ker(Chi_V)` と `im(Chi_V)=Q_E(V)` を
//! 確認できると述べる。ここで判定するのはその二つの等式と、商上の整数線形方程式の可解性である。
//! いずれも部分格子の相等と所属の判定に帰着するため、不変因子を経由せず列 HNF で決定する。
//! 出力は同じ真偽値であり、HNF は正準形なので相等判定に使える。
//!
//! 係数はすべて `i128` で保持し、桁溢れは `None`(判定不能)として fail-closed に返す。
//! 沈黙して誤った真偽値を返さないことを優先する。

/// 列ベクトルの集合が生成する部分格子。各要素は長さ `rows` の列。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lattice {
    rows: usize,
    /// 列 HNF の非零列。pivot 行は狭義単調増加。
    basis: Vec<Vec<i128>>,
    /// `basis[k]` の pivot 行。
    pivots: Vec<usize>,
    /// 生成元列 `G` に対し `G * transform = [basis | 0]` を満たす単模行列(列優先)。
    transform: Vec<Vec<i128>>,
}

impl Lattice {
    #[cfg(test)]
    pub(crate) fn rank(&self) -> usize {
        self.basis.len()
    }

    /// `Z^rows` 全体を生成するか。
    pub(crate) fn is_full(&self) -> bool {
        self.basis.len() == self.rows
            && self
                .pivots
                .iter()
                .enumerate()
                .all(|(index, pivot)| *pivot == index)
            && self
                .basis
                .iter()
                .enumerate()
                .all(|(index, column)| column[index] == 1)
    }

    /// 同じ部分格子か。HNF は正準形なので基底の一致で判定できる。
    pub(crate) fn equals(&self, other: &Lattice) -> bool {
        self.rows == other.rows && self.basis == other.basis && self.pivots == other.pivots
    }

    /// `target` がこの部分格子に属するか。属する場合は係数を返す。
    pub(crate) fn solve(&self, target: &[i128]) -> Option<Option<Vec<i128>>> {
        if target.len() != self.rows {
            return None;
        }
        let mut residue = target.to_vec();
        let mut coefficients = vec![0i128; self.basis.len()];
        for (index, pivot) in self.pivots.iter().enumerate() {
            let head = self.basis[index][*pivot];
            let value = residue[*pivot];
            if value == 0 {
                continue;
            }
            if head == 0 || value % head != 0 {
                return Some(None);
            }
            let quotient = value / head;
            coefficients[index] = quotient;
            for row in 0..self.rows {
                let scaled = quotient.checked_mul(self.basis[index][row])?;
                residue[row] = residue[row].checked_sub(scaled)?;
            }
        }
        if residue.iter().all(|value| *value == 0) {
            Some(Some(coefficients))
        } else {
            Some(None)
        }
    }

    pub(crate) fn contains(&self, target: &[i128]) -> Option<bool> {
        Some(self.solve(target)?.is_some())
    }

    /// 元の生成元列での係数を返す。`generators * x = target` の整数解。
    pub(crate) fn solve_generators(&self, target: &[i128]) -> Option<Option<Vec<i128>>> {
        let Some(basis_coefficients) = self.solve(target)? else {
            return Some(None);
        };
        let generator_count = self.transform.len();
        let mut solution = vec![0i128; generator_count];
        for (index, coefficient) in basis_coefficients.iter().enumerate() {
            if *coefficient == 0 {
                continue;
            }
            for row in 0..generator_count {
                let scaled = coefficient.checked_mul(self.transform[index][row])?;
                solution[row] = solution[row].checked_add(scaled)?;
            }
        }
        Some(Some(solution))
    }
}

/// 列の集合から部分格子を作る。`rows` は各列の長さ。
pub(crate) fn lattice_from_columns(columns: &[Vec<i128>], rows: usize) -> Option<Lattice> {
    if columns.iter().any(|column| column.len() != rows) {
        return None;
    }
    let mut transform = identity(columns.len());
    let (basis, pivots, _) = column_hnf(columns.to_vec(), rows, Some(&mut transform))?;
    Some(Lattice {
        rows,
        basis,
        pivots,
        transform,
    })
}

/// 行の集合(関係行列など)が張る部分格子。行を列として読み替える。
pub(crate) fn lattice_from_rows(rows_matrix: &[Vec<i128>], width: usize) -> Option<Lattice> {
    lattice_from_columns(rows_matrix, width)
}

/// `{ x in Z^n : matrix * x in sublattice }` を生成する列の集合を返す。
///
/// `matrix` は `rows x n`(列優先で `columns[j]` が第 j 列)、`sublattice` は
/// `Z^rows` の部分格子。合成写像 `Z^n -> Z^rows / sublattice` の核を与える。
pub(crate) fn preimage_kernel_columns(
    columns: &[Vec<i128>],
    rows: usize,
    sublattice: &Lattice,
) -> Option<Vec<Vec<i128>>> {
    let n = columns.len();
    if sublattice.rows != rows {
        return None;
    }
    // [ matrix | -sublattice_basis ] の核を取り、最初の n 成分へ射影する。
    let mut extended = columns.to_vec();
    for column in &sublattice.basis {
        let mut negated = Vec::with_capacity(rows);
        for value in column {
            negated.push(value.checked_neg()?);
        }
        extended.push(negated);
    }
    let mut transform = identity(extended.len());
    let (_, _, kernel_start) = column_hnf(extended, rows, Some(&mut transform))?;
    let mut projected = Vec::new();
    for column in transform.iter().skip(kernel_start) {
        projected.push(column[..n].to_vec());
    }
    Some(projected)
}

fn identity(size: usize) -> Vec<Vec<i128>> {
    (0..size)
        .map(|index| {
            let mut column = vec![0i128; size];
            column[index] = 1;
            column
        })
        .collect()
}

/// 列 HNF。`transform` を渡すと同じ列操作を適用し、`A * transform = H` を保つ。
/// 戻り値は (非零列, その pivot 行, 零列の開始位置)。
fn column_hnf(
    mut matrix: Vec<Vec<i128>>,
    rows: usize,
    mut transform: Option<&mut Vec<Vec<i128>>>,
) -> Option<(Vec<Vec<i128>>, Vec<usize>, usize)> {
    let count = matrix.len();
    if let Some(transform) = transform.as_deref()
        && transform.len() != count
    {
        return None;
    }
    let mut pivot_column = 0usize;
    let mut pivots = Vec::new();
    for row in 0..rows {
        loop {
            let nonzero = (pivot_column..count)
                .filter(|index| matrix[*index][row] != 0)
                .collect::<Vec<_>>();
            if nonzero.len() <= 1 {
                break;
            }
            // `i128::MIN.abs()` はラップして最小絶対値に化け、商が常に 0 になって
            // ループが進まなくなる。判定不能として返す。
            if nonzero
                .iter()
                .any(|index| matrix[*index][row] == i128::MIN)
            {
                return None;
            }
            let smallest = *nonzero
                .iter()
                .min_by_key(|index| matrix[**index][row].abs())
                .expect("nonzero column set is not empty");
            for index in nonzero {
                if index == smallest {
                    continue;
                }
                let quotient = matrix[index][row] / matrix[smallest][row];
                if quotient == 0 {
                    continue;
                }
                subtract_scaled(&mut matrix, index, smallest, quotient, rows)?;
                if let Some(transform) = transform.as_deref_mut() {
                    subtract_scaled(transform, index, smallest, quotient, count)?;
                }
            }
        }
        let Some(found) = (pivot_column..count).find(|index| matrix[*index][row] != 0) else {
            continue;
        };
        matrix.swap(pivot_column, found);
        if let Some(transform) = transform.as_deref_mut() {
            transform.swap(pivot_column, found);
        }
        if matrix[pivot_column][row] < 0 {
            negate(&mut matrix, pivot_column, rows)?;
            if let Some(transform) = transform.as_deref_mut() {
                negate(transform, pivot_column, count)?;
            }
        }
        // 正準形にするため、左側の列を pivot で法として簡約する。
        let head = matrix[pivot_column][row];
        for index in 0..pivot_column {
            let value = matrix[index][row];
            let quotient = value.div_euclid(head);
            if quotient == 0 {
                continue;
            }
            subtract_scaled(&mut matrix, index, pivot_column, quotient, rows)?;
            if let Some(transform) = transform.as_deref_mut() {
                subtract_scaled(transform, index, pivot_column, quotient, count)?;
            }
        }
        pivots.push(row);
        pivot_column += 1;
    }
    let basis = matrix[..pivot_column].to_vec();
    Some((basis, pivots, pivot_column))
}

fn subtract_scaled(
    matrix: &mut [Vec<i128>],
    target: usize,
    source: usize,
    quotient: i128,
    height: usize,
) -> Option<()> {
    for row in 0..height {
        let scaled = quotient.checked_mul(matrix[source][row])?;
        matrix[target][row] = matrix[target][row].checked_sub(scaled)?;
    }
    Some(())
}

fn negate(matrix: &mut [Vec<i128>], column: usize, height: usize) -> Option<()> {
    for row in 0..height {
        matrix[column][row] = matrix[column][row].checked_neg()?;
    }
    Some(())
}

/// 行優先の行列と列ベクトルの積。
pub(crate) fn matrix_vector(matrix: &[Vec<i128>], vector: &[i128]) -> Option<Vec<i128>> {
    let mut result = Vec::with_capacity(matrix.len());
    for row in matrix {
        if row.len() != vector.len() {
            return None;
        }
        let mut sum = 0i128;
        for (entry, value) in row.iter().zip(vector) {
            sum = sum.checked_add(entry.checked_mul(*value)?)?;
        }
        result.push(sum);
    }
    Some(result)
}

/// 行優先の行列を列の集合へ転置する。
pub(crate) fn columns_of(matrix: &[Vec<i128>], width: usize) -> Vec<Vec<i128>> {
    (0..width)
        .map(|column| {
            matrix
                .iter()
                .map(|row| row.get(column).copied().unwrap_or_default())
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 例 10.2 の semantic 側: `Z[sigma]/(2 sigma)` の関係が張るのは `2Z`。
    #[test]
    fn example_10_2_relation_lattice_is_two_z() {
        let relations = lattice_from_rows(&[vec![2]], 1).expect("relation lattice");
        assert_eq!(relations.rank(), 1);
        assert_eq!(relations.contains(&[2]), Some(true));
        assert_eq!(relations.contains(&[4]), Some(true));
        assert_eq!(relations.contains(&[1]), Some(false));
        assert!(!relations.is_full());
    }

    /// 例 10.2 の exactness: `chi(sigma)=[1]` の核は `ker(Z -> Z/(2)) = 2Z`。
    #[test]
    fn example_10_2_kernel_of_chi_is_the_relation_lattice() {
        let equation_relations = lattice_from_rows(&[vec![2]], 1).expect("equation relations");
        let chi_columns = columns_of(&[vec![1]], 1);
        let kernel_columns = preimage_kernel_columns(&chi_columns, 1, &equation_relations)
            .expect("kernel columns");
        let kernel = lattice_from_columns(&kernel_columns, 1).expect("kernel lattice");
        let repair_relations = lattice_from_rows(&[vec![2]], 1).expect("repair relations");
        assert!(kernel.equals(&repair_relations));
    }

    /// 例 10.2 の generation: `[1]` は `Z/(2)` を生成する。
    #[test]
    fn example_10_2_chi_image_generates_the_quotient() {
        let mut generators = vec![vec![2]];
        generators.extend(columns_of(&[vec![1]], 1));
        let spanned = lattice_from_columns(&generators, 1).expect("spanned lattice");
        assert!(spanned.is_full());
    }

    /// 生成が足りない場合は full にならない。
    #[test]
    fn insufficient_generation_is_detected() {
        let generators = vec![vec![2], vec![4]];
        let spanned = lattice_from_columns(&generators, 1).expect("spanned lattice");
        assert!(!spanned.is_full());
        assert_eq!(spanned.contains(&[2]), Some(true));
        assert_eq!(spanned.contains(&[1]), Some(false));
    }

    /// 二次元での核計算。`chi = [[1, 0]]`、equation 関係 `(3)` なら核は `{(x,y) : x in 3Z}`。
    #[test]
    fn preimage_kernel_in_rank_two() {
        let equation_relations = lattice_from_rows(&[vec![3]], 1).expect("equation relations");
        let chi_columns = columns_of(&[vec![1, 0]], 2);
        let kernel_columns = preimage_kernel_columns(&chi_columns, 1, &equation_relations)
            .expect("kernel columns");
        let kernel = lattice_from_columns(&kernel_columns, 2).expect("kernel lattice");
        assert_eq!(kernel.contains(&[3, 0]), Some(true));
        assert_eq!(kernel.contains(&[0, 1]), Some(true));
        assert_eq!(kernel.contains(&[1, 0]), Some(false));
    }

    /// rank が一致しても格子が違えば相等ではない。exactness を rank 比較へ弱める変異は
    /// これを通せない。
    #[test]
    fn equal_rank_does_not_imply_equal_lattice() {
        let two = lattice_from_rows(&[vec![2]], 1).expect("2Z");
        let four = lattice_from_rows(&[vec![4]], 1).expect("4Z");
        assert_eq!(two.rank(), four.rank());
        assert!(!two.equals(&four));
        assert_eq!(two.contains(&[4]), Some(true));
        assert_eq!(four.contains(&[2]), Some(false));
    }

    /// 部分格子の相等は生成元の取り方に依らない。
    #[test]
    fn lattice_equality_is_independent_of_the_generating_set() {
        let left = lattice_from_columns(&[vec![2, 0], vec![0, 3]], 2).expect("left");
        let right =
            lattice_from_columns(&[vec![2, 3], vec![0, 3], vec![4, 6]], 2).expect("right");
        assert!(left.equals(&right));
        let different = lattice_from_columns(&[vec![2, 0], vec![0, 6]], 2).expect("different");
        assert!(!left.equals(&different));
    }

    /// 商上の可解性と解の係数。
    #[test]
    fn solve_returns_coefficients_or_reports_no_solution() {
        let lattice = lattice_from_columns(&[vec![2, 0], vec![0, 5]], 2).expect("lattice");
        let solution = lattice.solve(&[4, 10]).expect("decidable");
        assert!(solution.is_some());
        let coefficients = solution.expect("solution exists");
        let reconstructed = matrix_vector(
            &[vec![2, 0], vec![0, 5]],
            &coefficients,
        )
        .expect("reconstruction");
        assert_eq!(reconstructed, vec![4, 10]);
        assert_eq!(lattice.solve(&[1, 0]).expect("decidable"), None);
    }

    /// 元の生成元での解を返す。冗長な生成系でも復元できる。
    #[test]
    fn solve_generators_returns_coefficients_of_the_supplied_columns() {
        let generators = vec![vec![2, 0], vec![0, 3], vec![2, 3]];
        let lattice = lattice_from_columns(&generators, 2).expect("lattice");
        let solution = lattice
            .solve_generators(&[4, 6])
            .expect("decidable")
            .expect("solution exists");
        assert_eq!(solution.len(), generators.len());
        let mut reconstructed = vec![0i128; 2];
        for (column, coefficient) in generators.iter().zip(&solution) {
            for (row, value) in column.iter().enumerate() {
                reconstructed[row] += value * coefficient;
            }
        }
        assert_eq!(reconstructed, vec![4, 6]);
        assert_eq!(lattice.solve_generators(&[1, 0]).expect("decidable"), None);
    }
}
