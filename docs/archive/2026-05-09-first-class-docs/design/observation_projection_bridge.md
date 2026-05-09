# Observation bridge と projection bridge の関係

このメモは Issue #80 の設計整理である。`ObservationFactorsThrough` と
projection bridge は、同じ `InterfaceProjection` を共有できるが、保証する
不変量は異なる。

## 結論

`ObservationFactorsThrough` は projection bridge の代替ではない。両者は
実装置換の局所契約層で並列に使う。

- projection bridge は、具象依存が抽象依存として sound に写ることを扱う。
- observation bridge は、観測可能な振る舞いが抽象を通じて因子化することを扱う。
- repository-level 集約、重みづけ、閾値設計は empirical / extractor tooling 側で扱う。

したがって、局所的な実装置換契約を Lean 側で読む場合の基本形は次である。

```text
DIPCompatible G π GA
and ObservationFactorsThrough π O
```

抽象グラフ上の辺を具体依存 witness へ戻して読む必要がある場合だけ、
`DIPCompatible` を `StrongDIPCompatible` に強める。

## 役割分担

`ProjectionSound G π GA` は、具象グラフ `G` の edge が抽象グラフ `GA` の
edge として表現されることを保証する。これにより、有限な測定 universe 上では
`projectionSoundnessViolation = 0` になる。これは依存構造の bridge であり、
観測値や振る舞いの同値性は主張しない。

`ObservationFactorsThrough π O` は、観測 `O.observe x` が `π.expose x` だけに
依存することを保証する。これにより `LSPCompatible π O` が従い、有限な測定
universe 上では `lspViolationCount = 0` になる。これは振る舞いの bridge であり、
依存 edge が抽象グラフに sound に写ることは主張しない。

このため、片方からもう片方は一般には従わない。projection bridge は構造保存、
observation bridge は置換可能性を測る behavioral extension として分離する。

## Lean theorem statement の扱い

Issue #80 では新しい Lean 定理は追加しない。現在の Lean にはすでに次の bridge が
あるため、両者の合成は新しい数学的主張ではなく、局所契約を束ねる packaging theorem
として扱える。

- `projectionSoundnessViolation_eq_zero_of_projectionSound`
- `lspCompatible_of_observationFactorsThrough`
- `lspViolationCount_eq_zero_of_observationFactorsThrough`
- `dipCompatible_of_strongDIPCompatible`

Issue #118 では、`LocalReplacementContract` を Lean に導入し、次の statement を
packaging theorem として追加した。

```text
LocalReplacementContract G π GA O ->
projectionSoundnessViolation G π GA components = 0
and lspViolationCount π O implementations = 0
```

ただし、この theorem は `components` と `implementations` の測定 universe を受け取る
包装補題であり、repository-level の重みづけや総合スコアは含めない。

## Issue #80 の結論

Issue #80 では、`ObservationFactorsThrough` と projection bridge の関係を
docs 上の設計整理として確定した。Issue #118 で局所契約 bundle と packaging theorem を
追加したため、Lean status は `LocalReplacementContract` が `defined only`、
`violationCounts_eq_zero_of_localReplacementContract` が `proved` である。
