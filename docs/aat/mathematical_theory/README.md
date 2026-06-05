# Atom 上の代数的アーキテクチャ論

Algebraic Architecture Theory, AAT は、ソフトウェアアーキテクチャに現れる
primitive architectural fact を Atom として置き、その合成で得られる構造を扱う。

Atom は、component の存在、関係の成立、capability の提供、状態の保持、
effect の発生、contract の成立、意味的解釈の付与などを一つの型付き事実として表す。
AAT は、これらの Atom が生成する代数を研究する。

```text
Atom
  -> Configuration
  -> ArchitectureObject
  -> Law
  -> Obstruction
  -> Flatness
  -> Operation
  -> Path / Homotopy / Diagram
  -> Analytic Representation
  -> Distance / Measure / Diagnostic Conclusion
```

AAT の基本形は次である。

```text
software architecture
  = atom-generated architecture object
  + law universe
  + obstruction calculus
  + operation algebra
  + geometric representation
  + analytic representation
  + distance representation
```

設計原則は slogan ではなく、Atom から生成された architecture object 上の
law、operation、preserved quantity として読む。architecture quality は単一値ではなく、
law、obstruction、path、transformation、representation の構造的振る舞いとして現れる。

## 構成

1. [第I部 Atom・対象・法則](part_1_atoms_objects_laws.md)
2. [第II部 平坦性・計算・幾何](part_2_flatness_calculus_geometry.md)
3. [第III部 解析表現・状態遷移代数・例](part_3_analytic_state_examples.md)
4. [第IV部 距離・測度・アーキテクチャ幾何](part_4_distance_measure_geometry.md)

## 中心図式

AAT の中心図式は次の合成である。

```text
AtomFamily
  -> AtomConfiguration
  -> ArchitectureObject
  -> InvariantFamily
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
  -> DistanceBundle
  -> BoundedDiagnosticConclusion
```

この図式に operation を作用させると、preservation、repair、extension、synthesis、
homotopy、diagram filling が得られる。解析表現を加えると、graph、matrix、state
transition algebra、curvature value による計算可能な読みが得られる。距離と測度を
加えると、lawful / unlawful、zero / nonzero、homotopic / not homotopic という二値的な
読みを、distance to lawfulness、signature drift、repair distance、filling cost として
定量化できる。
