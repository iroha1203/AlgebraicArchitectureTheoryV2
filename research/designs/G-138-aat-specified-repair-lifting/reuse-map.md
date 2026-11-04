# G-138：再利用・接続・新規証明の対応

調査したmainは `1d43ef5aa7c6f90973dec306fb87d7e8fcf2c408`。
Leanはv4.28.0、mathlibは `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
以下はsourceの型・前提・定義を読んだ設計であり、今回Leanの再検証は行っていない。
active化時は[カードの検査基準](../../../.codex/skills/target-theorem-loop/references/target-goal-contract.md)
に従いGOAL・設計・共通基準・使用宣言の版をtracking Issueへ固定する。

略記ODB=`AAT.AG.ObstructionDiagnosticBridge`、ADC=`AAT.AG.AtlasDefectComposition`。

## 1. 既存宣言の直接再利用

| ファイル・宣言 | 型・前提・利用内容 | 使用先 |
| --- | --- | --- |
| [FaceEmptyCechNormalization.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean)：ODB.GeneratorPresentationの`faceEmptyCechComplex`、`faceEmptyCechCochain0Equiv/1Equiv/2Equiv`、`faceEmptyCech_d0_normalizes`、`faceEmptyCech_d1_eq_zero` | `FaceEmptyAATCechCover`と空FaceComponent、非空・preconnected支持。元の係数層切断と整数presentation座標の加法同型 | Dの元複体と代表元を保存 |
| 同上：`actualCechCoefficientCochain0/1/2`、`actualCechCoefficient_comm0/1`、`actualCechCoefficientCochainMap` | adequate Law、有限Source。整数presentation群から有理Law座標への加法写像と微分可換性 | Dのφを生成 |
| [ActualCechH1Comparison.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean)：`actualCechDiagnosticH1Map`、`actual_cech_diagnostic_h1_map_additive_h1_class` | 元のAdditiveCechH1から診断H¹への加法準同型。係数を同じ体と仮定していない | 新しい標準H¹写像との実比較 |
| [SpecifiedAffineObstruction.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean)：`actualMismatch`、`actualCocycle`、`actual_mismatch_adjust_local_state`、`actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch` | transition+d(localState)から指定zを生成し、局所変更で微分が加わる | Dのz、元の修復への符号 |
| [SpecifiedClassReflection.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean)：`integralCorrection`、`actual_mismatch_eq_d_integralCorrection` | 任意の診断補正b、CommonLabelChartSupport、ReflectionCondition、元の診断等式から整数a₀を生成 | Bの条件a₀をDで放電 |
| [ActualCechReadingComparison.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechReadingComparison.lean)：`actualCechPullback0/1`、`actualCechPullback_comm0`、`coefficientCochain0_presentationPullback`、`actualCechCoefficient1_pullback_naturality`、`actualCechDiagnosticH1_naturality` | coarse/fineの既存nerve morphismと両実cover、adequacy。元の射と同じ座標で自然性 | CからDへのreading適用 |
| [FiniteIncidenceGeometry.lean](../../lean/ResearchLean/AG/VisibleCycleReflection/FiniteIncidenceGeometry.lean)：`upperTopology`、`chart`、`charts_cover`、`overlap_eq_singleton`、`table_geometry_valid` | 有限頂点・辺、単射な端点対、端点順序。原始incidenceから非空連結chartと重なりの幾何を構成 | W1の二chartの実被覆 |

G-125の受理証拠は[report](../../reports/G-125-aat-obstruction-diagnostic-bridge.md)と
[最終PR #4825](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4825)、
[受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4825#issuecomment-5746968898)。
G-132の受理証拠は[tracking Issue #5250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250)。
再利用時は上表の使用宣言と必要な定義・適用引数を受理版と照合する。
既存定理の名称や受理記録だけを新しい接続の証明にはしない。

## 2. 接続・一般化が必要な既存構成

| 既存資産 | そのままでは満たさない要求 | 新しい仕事 |
| --- | --- | --- |
| [ConeCoordinates.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeCoordinates.lean)：`coneCoordinateEquiv`、`coneCoordinateEquiv_d`、`coneCoordinateEquiv_map`、`comparisonConeMinusOneEquiv` | `ModuleCat ℚ`に固定。後者は三項複体 | 一般アーベル群の標準錐座標・零延長・全次数式を作る。ℚ特殊化で既存式へ一致させる |
| [ConeExactSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean)、[ConeEndDegrees.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeEndDegrees.lean) | 有理係数の実錐完全列・次元公式。整数torsionと指定元の対応は含まない | Bの整数加群のj,p・完全性・代表元を標準APIから構成 |
| G-125の元Čech/H¹型とthree-cochain診断型 | 一般の標準複体と型が違う | degreewise同型、微分、元H¹商、実φ、指定z,bを同じ可換図式で接続 |
| G-125のreading射 | 元のdegreewise APIから標準複体の平方へ接続する義務がある | 高次数の零性を放電し、同じ射の障害・全解・作用の自然性を証明 |
| Formal [LawGeneratedConormalFirstOrderDescentPackage.lean](../../../Formal/AG/SemanticRepair/Conormal/LawGeneratedConormalFirstOrderDescentPackage.lean)：`globalLiftH0Action_simplyTransitive` | 選ばれたconormal sequenceの大域liftを扱う。任意φの指定bのfiberとは対象が違う | 作用・差のAPI設計の参照先。これを候補18の証明として数えない |

G-133の既存錐の受理経路は[report](../../reports/G-133-aat-atlas-defect-composition.md)と
[tracking Issue #5261](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261)にある。
G-133のℚ APIを変更せず一般版をResearchへ追加する案を優先し、既存式との一致を確認する。
FormalからResearchへのimportは追加しない。

## 3. 新規証明・算法

- 一般のLift・指定錐類・零性同値と証人復元、余核障害と選択独立性。
- 同じj,pの短完全列、ker kφによる実作用、全解同値、全射・単射の全量化定理。
- 可換平方による障害・解・作用の自然性、同型時の両方向対応。
- 有限表示整数群の検査・decode、停止する整数消去、関係を除いた全解と不能証拠の生成。
- W1–W6の同時成立条件、W1の原始幾何からのG-125実比較、W2–W5の算法評価。

G-130 [FiniteElimination.lean](../../lean/ResearchLean/AG/RelativeRepairComposition/FiniteElimination.lean)
の `diagonal_exists`・`diagonalize` は体上、実行的探索は有限体の行列操作全列挙を使う。
整数のSNF生成・停止証明へそのまま適用できない。
調査した固定mathlibのMatrix/GroupTheoryにはSmith名の完成算法を確認できていない。
従ってEの整数producerを新規の主要証明義務として見積もる。実装時に同等APIが見つかった場合は
型・整数の全入力・停止・全解復元を照合して再利用し、Eの要求を縮小しない。

## 4. mathlibの接続先

固定mathlibの次のsourceを用いる。

- `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`：
  `CochainComplex.mappingCone`、`mappingCone.inl/inr/fst/snd`、`d_snd_v`、`d_fst_v`。
  一般の加法圏の標準錐であり、整数加群でも必要な圏のinstanceを構成して適用する。
- `Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean`：錐triangleと誘導写像。
  Bのj,pは代表元まで同定し、shiftの符号を確認する。
- `Mathlib/Algebra/AddTorsor/Defs.lean`、`Basic.lean`：`AddTorsor`。
  非空なLiftの加法作用・差と既存instance条件を対応させる。
- `Submodule`、`QuotientAddGroup`の核・像・商API：元の加法商と標準homologyの同定。
  有理線形商を忘却した場合も代表元評価を証明する。

## 5. Rust側の対応は用途・設計の参照

調査版の `tools/archsig_v0.6.0/crates/computation/src/observed/` には次がある。

| 実装 | 現在の責務 | 本GOALとの関係 |
| --- | --- | --- |
| `integer_fiber.rs`の`solve`、`change_result/linear_result.rs` | 整数系の特解・核・SNF表示 | Eの用途と算法設計の参照。RustをLean証拠としてimportしない |
| `local_integer_cech.rs`の`gluing` | 補正された局所値の同時方程式を解き、大域値を復元 | 持ち上げ計算の既存例。候補18で初めて可能になる機能ではない |
| `local_affine_compare.rs` | cochain可換性・H上の写像・核余核・類輸送 | 指定bのfiberへの将来の接続点 |
| `change_result.rs` | 元Assignmentの解・一意性とrepair条件 | W6の区別を保持する必要がある |

ArchSigの入力生成・再検査・出力仕様はToolingの責務とする。
今回のカードはRust変更・既存solverの再実装・キャッシュ改善を完了条件にしない。
