# Part VII proposition 3.6 statement contract

Issue #3198で固定する命題3.6のLean statement。selected finite directed graph
`G`について、length-indexed `CountedDirectedWalk G start finish n`を実際に数え、
adjacency matrix power entryとそのcardinalityを全自然数`n`で一致させる。

## Material data

- `G : FiniteDirectedGraphTarget Vertex Edge RelationLabel`: 本文のselected
  finite graph representation。
- `n : Nat`: walk length。`0`、`1`、任意のsuccessorを含む。
- `start finish : Vertex`: matrix entryとwalk endpoint。

walk cardinalityをprofile fieldや再帰countの別名として受け取らず、
`CountedDirectedWalk`型の`Fintype.card`として構成する。

## Decomposition statement

```lean
def CountedDirectedWalk.succEquiv
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    CountedDirectedWalk G start finish (n + 1) ≃
      Σ middle : Vertex,
        { e : Edge // G.source e = start ∧ G.target e = middle } ×
          CountedDirectedWalk G middle finish n

theorem CountedDirectedWalk.card_succ
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    [Fintype Vertex]
    (n : Nat) (start finish : Vertex) :
    Fintype.card (CountedDirectedWalk G start finish (n + 1)) =
      ∑ middle : Vertex,
        edgeFiberCard G start middle *
          Fintype.card (CountedDirectedWalk G middle finish n)
```

## Target statement

```lean
theorem adjacencyMatrixPower_apply_eq_countedDirectedWalk_card
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    (adjacencyMatrixPower G n) start finish =
      Fintype.card (CountedDirectedWalk G start finish n)
```

## Proof-use

- length zeroはendpoint equalityとの明示equivalenceで数える。
- length `n + 1`は`succEquiv`でmiddle vertex、first edge fiber、length `n`
  tailへ分解する。
- `card_succ`をmatrix multiplicationの有限和と接続し、`n`について帰納する。
- 最終statementは既存のmatrix-power recursionとactual walk-cardinality theoremを
  合成する。

length-one補題、結論相当profile field、positivityだけのexistence theoremは
一般cardinality theoremの代用にしない。weighted infinite graph、一般measure、
ArchSig graph analysisは主張しない。
