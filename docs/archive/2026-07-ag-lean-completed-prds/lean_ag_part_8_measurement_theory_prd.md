# AAT代数幾何版 Lean形式化 PRD-8: 第VIII部 Measurement Theory

対象本文: [第VIII部 Measurement Theory](algebraic_geometric_theory/part_8_measurement_theory.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md) /
[PRD-4 第IV部](lean_ag_part_4_obstruction_cohomology_prd.md) /
[PRD-5 第V部](lean_ag_part_5_derived_law_geometry_repair_prd.md) /
[PRD-6 第VI部](lean_ag_part_6_singularity_monodromy_stack_prd.md) /
[PRD-7 第VII部](lean_ag_part_7_representation_periods_analysis_prd.md)

## 問い

第VII部までで readable になった AAT geometry は、どの条件の下で measurably readable になるか。
すなわち、構成済みの geometry / reading layer の上に、次の measurement layer を Lean 上で
sorry なしに立ち上げられるか。

```text
AATGeometry
  -> representation / period / metric reading
  -> MeasurementProfile M
  -> FiniteMeasurementRegime M
  -> MeasurementVerdict_M(alpha)
  -> MeasurementPacket_M
```

特に、次を機械検証できるか。

- `measured_zero`、`measured_nonzero`、`unmeasured`、`unknown`、`not_computed` を
  型として分離し、`unmeasured != zero`、`unknown != nonzero` を崩さないこと
  (定義3.1 / 原則3.2 / 定義3.3)。
- finite measurement regime の下で、Čech cohomology、obstruction cocycle、
  Stanley-Reisner complex、monomial Tor、support of conflict class が、有限線形代数・有限表示加群計算・
  有限組合せ計算へ落ちること(定理4.2)。
- finite square-free regime で、obstruction ideal が Stanley-Reisner ideal として読め、
  Alexander dual が minimal repair hitting set を与えること(定理5.2)。
- refactor equivalence が finite site、ringed ambient、coefficient、law ideal、witness / axis reading を
  同型的に保存する場合、selected obstruction class の zero verdict が保存されること(定理7.3)。
- finite inner-product cochain model で Hodge decomposition、harmonic representative、harmonic debt minimality、
  essential repair lower bound が証明できること(定理8.5 / 8.6 / 系8.7)。
- common ambient と support-localized pairing を固定した場合、repair direction が transferred residue を持つ
  sufficient condition を証明できること(定理10.3)。
- 第VIII部の selected measurement packet が bounded mathematical measurement として synthesis でき、
  AAT-GAGA finite measurement comparison が certified 部分と theorem-candidate interface を分離して束ねられること
  (定理12.1 / 定理12.3)。

採否規律: measurement profile / verdict / finite computability / finite combinatorial repair / refactor transport /
cellular sheaf Laplacian / LawConflict measurement / support-localized transfer / measurement packet の構成と、
CBI 定理(4.2 / 5.2 / 7.3 / 8.5 / 8.6 / 10.3 / 12.1 / 12.3)および系8.7に寄与する定義・命題だけを
形式化対象に採る。寄与しない要素(例、原則、自然言語の警句、未選択の外部手続き)は対象外とする。
実装中に、finite computability、verdict discipline、Hodge decomposition、transfer measurement、AAT-GAGA comparison に
必要な仮定が本文に不足している、または第II〜VII部の形式化と接続できないことが見つかった場合、
それは本文または本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1〜7 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`admit`・`sorry`・`unsafe` 禁止 /
Mathlib 二段橋 / 台帳統合 / 先行PRD依存の blocked 規律 / 部番号付き台帳ラベル)。

本PRDで新たに加わる方針が五つある。

**(1) measurement は profile に相対化された record discipline として実装する。**

第VIII部は「何でも測れる」ことを主張しない。Lean では、まず

```text
MeasurementProfile M
FiniteMeasurementRegime M
MeasurementPacket M
```

を定義し、どの site、cover、coefficient、law universe、witness variables、representation family、
zero / nonzero predicate、certificate selector の範囲で測るのかを record として固定する。
`Measured_M(alpha)` は `alpha` が `M` の domain に入っていることを含む bounded statement として扱う。

**(2) verdict は enum ではなく依存データ付きの構造として扱う。**

`measured_zero` と `measured_nonzero` は、それぞれ selected predicate と certificate によって支えられる。
`unmeasured` は scope 外、`unknown` は scope 内 undecided、`not_computed` は未実行または unavailable である。
Lean では constructors の disjointness だけでなく、各 verdict の payload を明示し、
`Zero_M` と `NonZero_M` が論理補集合でないことを設計として保つ。

**(3) finite computability は algorithm completeness ではなく effective interface への reduction である。**

第VIII部の計算可能性は、`EffCoeff_M` が提供する有限線形代数・有限表示加群・ideal-membership・resolution 選択に
相対化される。Lean 上では、任意の coefficient category の決定可能性を主張せず、

```text
EffCoeff_M supplies exactly the procedures used by M.
```

という interface を仮定として持つ。定理4.2は、selected invariants をその interface が扱える有限 object へ落とす
certified bounded inference として証明する。

**(4) stability / base change / lower bound / spectral hotspot は theorem-candidate として statement-only に分ける。**

第VIII部には、Finite Čech Stability、Monotone Witness Stability、Morse Lower Bound、Flat Base Change、
Transfer Lower Bound、Spectral Hotspot、Wasserstein lower bound などの theorem candidate が含まれる。
これらは Prop / structure statement としてコンパイルが通る形で形式化し、証明しない。
証明済みの CBI theorem と candidate-dependent interface が混ざらないよう、theorem package の field で明示的に分ける。

**(5) AAT-GAGA は finite profile 内の比較 interface であり、外部忠実性ではない。**

定理12.3は、Hodge comparison、period accounting、topological capacity、derived conflict accounting などを
selected finite measurement profile の中で束ねる。名前の `GAGA` は比喩であり、未選択の data source、
外部 procedure、全 law universe、任意の analytic smallness から lawfulness を結論しない。
Lean では certified components と candidate-regime components を別フィールドに持つ comparison package として実装する。

## 背景

- PRD-7 は、AAT geometry を representation、period、metric、mass、repair cost として読む analytic layer を定義した。
  第VIII部は、その reading が finite / effective / verdict-disciplined profile の下で measurement になる条件を与える。
- PRD-2 の finite poset AAT site regime と有限 Čech 計算、PRD-4 の obstruction cohomology / Stokes accounting / topological debt、
  PRD-5 の LawConflict / Tor / Hilbert series / transfer pairing、PRD-7 の metric / distance / representation reading が、
  本PRDの主要依存先である。
- 第VIII部の theorem 4.2 は、finite site、finite cover、effective coefficient、finite witness variables、selected finite resolutions を
  一つの measurement profile に束ねる。これは後続の ArchSig 型 proof-carrying measurement ledger に相当する Lean 側の理論アンカーになる。
- 第IX部は evolution geometry に進む。第VIII部は静的な selected profile の measurement に留まり、temporal law / trace category / state transition presheaf は扱わない。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. `MeasurementProfile`、`FiniteMeasurementRegime`、`MeasurementVerdict`、`VerdictData`、`StructuralVerdict`、`AnalyticReading` が Lean 上に存在する。
2. `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` の区別が型と補題で保証され、`unmeasured` を zero として扱う経路が存在しない。
3. Finite AAT Computability(定理4.2)が theorem package として存在し、selected invariants が finite linear algebra / finite presented module / finite combinatorics / finite resolution computation へ落ちることが証明されている。
4. Stanley-Reisner / Alexander Dual Repair Theorem(定理5.2)が証明され、minimal forbidden supports、minimal vertex covers、minimal repair hitting sets の対応が機械検証されている。
5. persistence / zigzag / Morse / monotone witness stability の statement-only interface が存在し、証明済み measurement theorem と混同されない。
6. Refactor Invariance under Equivalence(定理7.3)が証明され、measurement profile equivalence の下で selected zero verdict が保存される。
7. Cellular sheaf Laplacian、finite Hodge decomposition、harmonic debt minimality、essential repair lower bound が Lean 上に存在する。
8. Common ambient LawConflict measurement、flat base change candidate、support-localized transfer measurement、Wasserstein transfer cost reading が形式化されている。
9. Finite Measurement Synthesis(定理12.1)と AAT-GAGA Finite Measurement Comparison(定理12.3)が theorem package として存在する。
10. PRD-1〜7 の有限モデルが measurement profile の golden examples へ拡張され、pseudo-circle、square-free hitting set、Hodge toy model、transfer toy model、measurement packet の実例が検証されている。
11. 第VIII部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第VIII部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 AAT Measurement Profile | 定義 | `M` の record。finite site / cover / coefficient / EffCoeff / Ob / law universe / witness / ideal / Rep / Dom / Zero / NonZero / Cert / Verdict を持つ(R1) |
| 原則2.2 Measurement Is Internal | 対象外 | 非主張に記録。profile 内部の bounded reading として設計に反映 |
| 定義3.1 Measurement Verdict | 定義+証明 | 5 verdict と `VerdictData_M(alpha)`。constructors の disjointness と payload 条件を補題化(R1) |
| 原則3.2 Verdict Boundary | 定義+証明 | `unmeasured != measured_zero`、`unknown != measured_nonzero`、`not_computed != unmeasured` を補題にする(R1) |
| 定義3.3 Structural Verdict and Analytic Reading | 定義 | structural verdict と analytic reading を別型に分ける(R1) |
| 定義4.1 Finite Measurement Regime | 定義 | finite poset site、finite/effective coefficient、explicit maps、finite witnesses、finite resolutions(R2) |
| 定理4.2 Finite AAT Computability [CBI] | 証明 | selected invariants を finite computation objects へ落とす theorem package(R2) |
| 定義5.1 Square-Free Repair Regime | 定義 | finite witness set、`Forb_U`、`MinForb_U`、square-free obstruction ideal(R3) |
| 定理5.2 Stanley-Reisner / Alexander Dual Repair Theorem [CBI] | 証明 | PRD-3 の SR theorem を再利用し、Alexander dual / hitting set 対応を追加(R3) |
| 原則5.3 Repair Hitting Set Is Not Repair Semantics | 対象外 | 非主張に記録。operation semantics は別 profile |
| 定義5.4 Discrete Morse Repair Reading | 定義 | acyclic matching / discrete Morse function を selected combinatorial repair route として読む(R3) |
| 定理候補5.5 Morse Lower Bound for Structural Repair | statement のみ | critical cells が collapse-style repair steps の下界になる candidate。operation semantics compatibility を仮定(R3) |
| 定義6.1 Witness Perturbation Distance | 定義 | forbidden support family の対称差距離、single update(R4) |
| 定義6.2 Persistence / Zigzag Reading | 定義 | monotone persistence module と finite zigzag module の interface(R4) |
| 定理候補6.3 Finite Čech Stability | statement のみ | finite zigzag / persistence stability distance に対する Lipschitz 型 candidate(R4) |
| 原則6.4 Stability Is a Measurement Assumption | 対象外 | 非主張に記録 |
| 定理候補6.5 Monotone Witness Stability | statement のみ | monotone forbidden-support filtration の bottleneck stability candidate(R4) |
| 定義7.1 Refactor Morphism of Measurement Profiles | 定義 | finite/ringed site morphism、law compatibility、coefficient comparison、witness / axis compatibility(R5) |
| 定義7.2 Pullback of Obstruction Classes | 定義 | Čech / sheaf cohomology pullback reading。pushforward は追加構造がある場合だけ(R5) |
| 定理7.3 Refactor Invariance under Equivalence [CBI] | 証明 | site equivalence、ringed ambient iso、coefficient iso、law ideal iso、witness / axis preservation 下の zero iff(R5) |
| 原則7.4 Monodromy Requires Functoriality | 対象外 | 非主張に記録。operation groupoid / coefficient transport がなければ monodromy measurement なし |
| 定義8.1 Cellular Measurement Model | 定義 | finite cell / incidence category と finite-dimensional inner product coefficient sheaf(R6) |
| 定義8.2 Sheaf Laplacian | 定義 | `L_n = d_{n-1}d_{n-1}^* + d_n^*d_n`(R6) |
| 定義8.3 Distance-to-Flatness Reading | 定義 | residual norm と projection-defined distance reading(R6) |
| 原則8.4 Near-Flat Is Not Lawful | 対象外 | 非主張に記録。small residual は structural zero ではない |
| 定理8.5 Finite Hodge Decomposition [CBI] | 証明 | finite-dimensional Hilbert complex の直交分解と `ker L_n ≅ H^n`(R6) |
| 定理8.6 Harmonic Debt Minimality [CBI] | 証明 | `min_c ||g - d_0 c|| = ||h(g)||`。直交射影で証明(R6) |
| 系8.7 Essential Repair Lower Bound | 証明 | repair cost の Lipschitz assumption 下で `||h(g)|| / L` 下界(R6) |
| 定義8.8 Spectral Gap Reading | 定義 | `lambda_1^+(L_1)` as analytic stability indicator(R6) |
| 定義8.9 Curvature Transfer Spectrum | 定義 | finite weighted directed graph / adjacency operator / spectrum reading(R6) |
| 定理候補8.10 Spectral Hotspot Reading | statement のみ | Perron-Frobenius regime の hotspot candidate(R6) |
| 定義9.1 Common Ambient Pair | 定義 | common ringed site / ideals / compatible coefficients / witness pair(R7) |
| 定理候補9.2 Flat Base Change Stability for LawConflict | statement のみ | flatness / finite presentation / coefficient compatibility 下の Tor base change candidate(R7) |
| 原則9.3 No Ambient, No Conflict Comparison | 対象外 | 非主張に記録 |
| 定義10.1 Support-Localized Repair Path | 定義 | conflict class support と repair path / direction の交差 predicate(R8) |
| 定義10.2 Transfer Measurement Pairing | 定義 | transfer target、zero / nontrivial predicate、norm、pairing(R8) |
| 定理10.3 Support-Localized Transfer [CBI] | 証明 | nontrivial pairing が nontrivial transferred residue を与える sufficient condition(R8) |
| 定理候補10.4 Transfer Lower Bound | statement のみ | nondegenerate pairing / support weight / projection norm 下界 candidate(R8) |
| 原則10.5 Transfer Non-Implications | 対象外 | 非主張に記録 |
| 定義10.6 Wasserstein Transfer Cost | 定義 | finite support graph 上の `W_1` optimal transport reading(R8) |
| 定理候補10.7 Transfer Cost Lower Bound | statement のみ | mass preservation と ground distance 下の `W_1` 下界 candidate(R8) |
| 定義11.1 AAT Measurement Packet | 定義 | profile / structuralVerdict / computedInvariants / analyticReadings / assumptions / nonConclusions(R9) |
| 原則11.2 Measurement Packet Is Bounded | 対象外 | 非主張に記録。packet fields で反映 |
| 定理12.1 Finite Measurement Synthesis [CBI] | 証明 | finite regime + adequacy + exactness + common ambient + pairing + verdict discipline から packet を返す(R9) |
| 原則12.2 What Part8 Adds | 対象外 | 非主張に記録 |
| 定理12.3 AAT-GAGA Finite Measurement Comparison [CBI] | 証明 | Hodge / harmonic / Stokes / capacity / Tor-Hilbert / stability interface を finite profile 内で束ねる(R10) |
| 原則12.4 AAT-GAGA Boundary | 対象外 | 非主張に記録 |

## 要求

### R0. 前提の確認と Formal/AG/Measurement の立ち上げ

- 本PRDの実装は PRD-2(`Formal/AG/Site`)、PRD-3(`Formal/AG/LawAlgebra`)、
  PRD-4(`Formal/AG/Cohomology`)、PRD-5(`Formal/AG/Derived`)、
  PRD-6(`Formal/AG/SingularityMonodromyStack`)、PRD-7(`Formal/AG/RepresentationAnalysis`)の成果物に依存する。
  着手時に依存宣言の存在を確認し、未実装の場合は `blocked` として tracking Issue に記録する。
  先行PRDの実装を本PRDのループで先取りしない。
- 第VIII部のモジュールを `Formal/AG/Measurement/` 以下に実装する。
  ファイル分割は本文の節構成に概ね対応させる。例:
  `Profile.lean`, `Verdict.lean`, `FiniteRegime.lean`, `Computability.lean`,
  `SquareFreeRepair.lean`, `Stability.lean`, `RefactorTransport.lean`,
  `CellularLaplacian.lean`, `Hodge.lean`, `LawConflictMeasurement.lean`,
  `SupportTransfer.lean`, `Wasserstein.lean`, `Packet.lean`, `GAGA.lean`, `Examples.lean`。
- ルート import に追加し、CI の `lake build` 対象に含める。
- PRD-9 の trace category / temporal coefficient / evolution geometry は導入しない。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. Measurement Profile と Verdict Discipline(定義2.1、3.1、3.3、原則3.2)

- `MeasurementProfile` を record として定義する。

```text
MeasurementProfile:
  X_M              -- finite site or site candidate
  U_M              -- selected cover / hypercover fragment
  k_M              -- coefficient ring / field
  EffCoeff_M       -- effective coefficient interface
  Ob_M             -- coefficient sheaf
  LawUniverse U
  WitnessVariables E
  I_Ob^U
  Rep_M
  Dom_M
  Zero_M
  NonZero_M
  Cert_M
  Verdict_M
```

- `Measured_M(alpha)` を、`alpha ∈ Dom_M` と selected method/certificate data を参照する bounded predicate として定義する。
- `MeasurementVerdict_M(alpha)` を依存データ付き inductive / structure として定義する。

```text
measured_zero    : InScope_M alpha -> Zero_M alpha -> CertRef_M alpha -> MeasurementVerdict_M alpha
measured_nonzero : InScope_M alpha -> NonZero_M alpha -> CertRef_M alpha -> MeasurementVerdict_M alpha
unmeasured       : OutOfScope_M alpha -> MeasurementVerdict_M alpha
unknown          : InScope_M alpha -> Undecided_M alpha -> MeasurementVerdict_M alpha
not_computed     : NotRunOrUnavailable_M alpha -> MeasurementVerdict_M alpha
```

- constructors の disjointness を証明する。

```text
unmeasured alpha != measured_zero alpha
unknown alpha != measured_nonzero alpha
not_computed alpha != unmeasured alpha
```

- `Zero_M` と `NonZero_M` が補集合であるとは仮定しない。補集合として使う theorem は置かず、必要な場合は explicit decidability assumption を別 predicate にする。
- structural verdict と analytic reading を別型として定義し、analytic value から structural verdict への暗黙変換を置かない。
- 完了条件: 定義群と verdict boundary 補題が sorry なしで存在する。

### R2. Finite Measurement Regime と定理4.2(定義4.1、定理4.2)

- `FiniteMeasurementRegime M` を定義する。少なくとも次の fields / predicates を持つ。

```text
X_M is finite poset site.
U_M is finite cover or finite hypercover fragment.
Ob_M is finite-dimensional over explicit field, or finitely presented in EffCoeff_M.
restriction maps are explicit matrices or finite module homomorphisms.
EffCoeff_M supplies kernel / image / quotient / ideal-membership procedures used by M.
zero / nonzero predicates are certificate-backed.
E is finite.
I_Ob^U is finitely generated.
selected Tor computations have finite free / Koszul / Taylor / monomial resolutions.
```

- `EffCoeff_M` を、実際に使う有限手続きと証明 certificate を返す interface として定義する。
  任意の係数圏の決定可能性を仮定しない。
- 定理4.2を theorem package として証明する。package は、次の selected invariants について finite representation object を返す。

```text
FiniteCechComplexRepresentation
FiniteCocycleRepresentative
FiniteVerdictComputationObject
FiniteSquareFreeObstructionIdeal
FiniteStanleyReisnerComplex
FiniteMonomialTorComplex
FiniteConflictSupport
```

- finite-dimensional field coefficient の場合は finite linear algebra、finitely presented `EffCoeff_M` の場合は提供された algorithms に reduction する。
- Tor は PRD-5 の finite free / Koszul / Taylor resolution interface を使う。Scarf / arbitrary minimal resolution を新規開発しない。
- 完了条件: 定理4.2 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R3. Stanley-Reisner / Alexander Dual Repair と Discrete Morse(定義5.1、定理5.2、定義5.4、定理候補5.5)

- square-free repair regime を PRD-3 の square-free witness regime から measurement profile に持ち上げる。

```text
SquareFreeRepairRegime M:
  finite E
  Forb_U : Finset (Finset E)
  MinForb_U
  I_Ob^U = < x_S | S in MinForb_U >
  Delta_U = { T | no S in MinForb_U, S ⊆ T }
```

- Alexander dual complex `Delta_U^vee`、minimal vertex cover、minimal witness hitting set、minimal repair hitting set を定義する。
- 定理5.2を証明する。

```text
I_Ob^U = I_{Delta_U}
minimal generators of I_{Delta_U} <-> minimal forbidden supports
minimal vertex covers of MinForb_U <-> minimal witness hitting sets
minimal generators of I_{Delta_U^vee} <-> minimal repair hitting sets
```

- `repair hitting set` は operation semantics ではないことを docstring と非主張に記録する。
- discrete Morse repair reading を、finite simplicial complex 上の acyclic matching / discrete Morse function として定義する。
- 定理候補5.5を statement-only で形式化する。critical cell count が selected collapse-style structural repair route の手数下界になるには、
  operation semantics compatibility、legality、side-effect profile を仮定に含める。
- 完了条件: 定理5.2 が sorry なしで証明され、定理候補5.5 の statement がコンパイルされている。

### R4. Witness Perturbation・Persistence・Stability Candidates(定義6.1、6.2、定理候補6.3、6.5)

- witness perturbation distance を finite forbidden support family の対称差距離として定義する。

```text
d_wit(F,F') = |F △ F'|
```

- single update、face insertion / deletion、collapse / anticollapse の reading を finite complex の update data として定義する。
- monotone persistence module と finite zigzag module の interface を定義する。

```text
PersistenceProfile:
  F_0 <= F_1 <= ... <= F_m
  complexes Delta_{F_i}
  coefficient comparison maps
  finite type condition
  stability distance d_stab

ZigzagProfile:
  F_0 <-> F_1 <-> ... <-> F_m
  oriented arrows / correspondences
  coefficient comparison maps
```

- 定理候補6.3を statement-only で形式化する。

```text
d_stab(H^*(F), H^*(F')) <= C_M * d_wit(F,F')
```

- 定理候補6.5を statement-only で形式化する。

```text
d_bottleneck(Barcode(F), Barcode(F')) <= d_wit(F,F')
```

- stability theorem がない measurement value は stable measurement ではないことを非主張に記録する。
- 完了条件: 定義群と statement 群がコンパイルされている。

### R5. Refactor Functoriality and Class Transport(定義7.1、7.2、定理7.3)

- measurement profiles `M_X`、`M_Y` の間の refactor morphism を定義する。

```text
rho : X_M -> Y_M
rho# : O_{Y_M} -> rho_* O_{X_M}
law compatibility : rho^{-1} I_Ob^{U,Y} -> I_Ob^{U,X}
coefficient comparison : rho^{-1} Ob_Y -> Ob_X
witness / axis compatibility
```

- coefficient comparison が固定されている場合に、Čech cohomology / cover-relative cohomology の pullback reading を定義する。

```text
rho^* : H^n(Y_M, Ob_Y) -> H^n(X_M, Ob_X)
```

- pushforward は finite map、trace map、aggregation rule などが追加された場合だけ別 interface として定義する。
- 定理7.3を証明する。仮定はすべて theorem 引数として明示する。

```text
rho is equivalence of selected finite sites.
ringed ambient comparison is iso.
coefficient comparison is iso.
law ideals pull back isomorphically.
witness and axis readings are preserved.
```

結論:

```text
alpha = 0 iff rho^* alpha = 0
```

- period pairing の preservation は chosen representatives / pairings compatibility がある場合の optional corollary とする。
- 完了条件: 定理7.3 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R6. Cellular Sheaf Laplacian・Hodge・Harmonic Debt(定義8.1–8.3、定理8.5、8.6、系8.7、定義8.8、8.9、定理候補8.10)

- cellular measurement model を定義する。最小実装では finite incidence category / finite cochain complex を一次対象にしてよい。

```text
CellularMeasurementModel:
  finite cells / incidence category
  finite-dimensional inner product spaces F(c)
  linear restriction maps
  cochain groups C^n(X_M,F)
  coboundary d_n
  adjoints d_n^*
```

- sheaf Laplacian を定義する。

```text
L_n = d_{n-1} d_{n-1}^* + d_n^* d_n
```

- residual norm `Res_M(s) = ||d_0 s||` と projection-defined `dist_flat_M(s)` を analytic reading として定義する。
  `dist_flat_M(s) = 0 -> lawful` の theorem は置かない。
- 定理8.5を、finite-dimensional real / complex inner product regime の Hilbert complex theorem として証明する。

```text
C^n = im d_{n-1} ⊕ ker L_n ⊕ im d_n^*
ker L_n ≅ H^n(X_M,F)
```

- 定理8.6を証明する。

```text
min_c || g - d_0 c || = || h(g) ||
```

- 系8.7を証明する。repair cost と cochain norm の `L`-Lipschitz 仮定、大域 lawful state への route が harmonic mismatch を解消する仮定を theorem 引数に取る。

```text
repair_cost >= ||h(g)|| / L
```

- spectral gap reading と curvature transfer spectrum を定義する。
- 定理候補8.10を statement-only で形式化する。Perron-Frobenius theorem を必要とする場合は future proof obligation として台帳に登録する。
- 完了条件: 定理8.5 / 8.6 / 系8.7 が sorry なしで証明され、定義8.8 / 8.9 と定理候補8.10 statement が存在する。

### R7. LawConflict Measurement and Base Change(定義9.1、定理候補9.2)

- common ambient pair を定義する。

```text
CommonAmbientPair(U,V):
  (X,O_X)
  I_U, I_V ⊆ O_X
  compatible coefficient objects
  selected witness pair and comparison profile
```

- common ambient があるときだけ LawConflict measurement を定義する。

```text
LawConflict_i^M(U,V) = Tor_i^{O_X}(O_X/I_U, O_X/I_V)
```

- 異なる topology / coefficient ring / ambient scheme の law ideals は comparison morphism なしに比較しないことを非主張として記録する。
- 定理候補9.2を statement-only で形式化する。affine case と sheaf/ringed-site case の二つの statement を分けてよい。

```text
Tor_i^A(A/I_U,A/I_V) ⊗_A A'
  ≅ Tor_i^{A'}(A'/I_U',A'/I_V')
```

仮定には flatness、finite presentation、coefficient compatibility、support pullback を含める。
- 完了条件: common ambient 定義と base-change candidate statements がコンパイルされている。

### R8. Support-Localized Transfer Measurement と Wasserstein Cost(定義10.1、10.2、定理10.3、定理候補10.4、定義10.6、定理候補10.7)

- selected conflict class `kappa_{U,V}` と support `Supp(kappa_{U,V})` を持つ support-localized repair path / direction を定義する。

```text
image(r) intersects Supp(kappa)
-- or
support(v) intersects Supp(kappa)
```

- transfer measurement pairing を定義する。

```text
TransRes_{U,V}
0_{TransRes}
Nontrivial_{TransRes}
|| - ||_{TransRes}
< -, - >_{U,V} : T_X x LawConflict_1(U,V) -> TransRes_{U,V}
```

- 定理10.3を証明する。

```text
Nontrivial(<v,kappa>_{U,V})
  -> selected repair direction has nontrivial transferred residue
```

これは sufficient condition であり、necessary condition には detecting pairing assumption を別途要求する。
- 定理候補10.4を statement-only で形式化する。normed target、nondegenerate pairing、support weight、projection norm、constant `lambda_M` を仮定に含める。
- finite support graph と ground distance に対して Wasserstein transfer cost を定義する。一般 measure theory ではなく finite optimal transport / transportation plan interface として始める。
- 定理候補10.7を statement-only で形式化する。

```text
W_1 >= m * dist(s, Abs)
```

- 完了条件: 定理10.3 が sorry なしで証明され、Wasserstein reading と candidate statements が存在する。

### R9. Measurement Packet と Finite Measurement Synthesis(定義11.1、定理12.1)

- `MeasurementPacket` を record として定義する。

```text
MeasurementPacket:
  profile
  structuralVerdict
  computedInvariants
  analyticReadings
  assumptions
  nonConclusions
```

- `computedInvariants` は、`H^n`、`Tor_i`、generators、supports、dimensions、ranks、representatives を含む optional / dependent fields として定義する。
- `analyticReadings` は、distance、mass、spectrum、residual norm、harmonic mass、barcode、repair cost、Wasserstein transfer cost、Morse collapse reading、monodromy index を含む。
- `nonConclusions` に、unselected laws、unmeasured support、unprovided coefficient data、undecided predicates を明示的に持たせる。
- 定理12.1を証明する。仮定:

```text
M is finite measurement regime.
cover is U-adequate.
witness and axis exactness hold where reflection is claimed.
coefficient objects are finite/effective and explicit under EffCoeff_M.
common ambient exists for selected LawConflict readings.
support-localized pairing is fixed for transfer readings.
verdict discipline distinguishes zero, nonzero, unmeasured, unknown, not_computed.
```

結論: selected measurement packet が bounded mathematical measurement として構成される。
- theorem candidate に依存する readings は、packet 内で `candidateInterface` または `conditionalReading` として certified verdict から分離する。
- 完了条件: 定理12.1 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R10. AAT-GAGA Finite Measurement Comparison(定理12.3)

- `AATGAGAComparisonPacket` を定義する。certified fields と candidate-interface fields を分ける。

Certified fields:

```text
HodgeComparison: H^n(X_M,F) ≅ ker L_n
HarmonicDecomposition
PeriodStokesAccounting
TopologicalDebtCapacity
DerivedConflictAccounting via Tor / Hilbert-series accounting
```

Candidate-interface fields:

```text
MonotoneWitnessStabilityInterface
FiniteCechStabilityInterface
FlatBaseChangeInterface
SpectralHotspotInterface
TransferLowerBoundInterface
```

- 定理12.3を証明する。finite measurement regime、finite cover、inner-product coefficient sheaf、cellular cochain model、square-free regime、common ambient、
  stability distance / comparison maps where applicable を仮定に取る。
- theorem candidate に依存する条項は certified conclusion ではなく、candidate regime が追加された場合の interface として返す。
- `GAGA` が外部 data source や external procedure の忠実性を主張しないことを docstring と非主張に記録する。
- 完了条件: 定理12.3 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R11. 有限モデルの拡張

- PRD-1〜7 の有限モデル(`Formal/AG/Examples/`)を第VIII部の水準へ拡張する。
  (a) pseudo-circle measurement profile: PRD-4 の擬円周 boundary model を `MeasurementProfile` に載せ、
      concrete cocycle の verdict が `measured_nonzero` になり、unmeasured axes が zero と混同されないことを検証する。
  (b) square-free hitting set example: 付録の `{p,q}` / `{q,r}` forbidden supports から、minimal repair hitting sets `{q}` と `{p,r}` を検証する。
  (c) finite computability example: 小さい finite poset site と finite coefficient sheaf で Čech complex、kernel / image / quotient object が `FiniteMeasurementRegime` に入ることを検証する。
  (d) refactor invariance example: finite site equivalence と coefficient iso の下で selected obstruction class の zero verdict が保存されることを検証する。
  (e) cellular Hodge example: 低次 finite cochain complex で `ker L_1 ≅ H^1` と harmonic debt minimality を検証する。
  (f) support-localized transfer example: finite-dimensional pairing で nontrivial residue verdict を返す例を検証する。
  (g) measurement packet / AAT-GAGA example: certified readings と candidate-interface readings が分離された packet を構成する。
- これらは第IX部 evolution geometry の static measurement fixtures として再利用できる形を保つ。
- 完了条件: (a)–(g) が sorry なしで存在する。

### R12. 台帳整備

- `lean_theorem_index.md` の AG 節に第VIII部の宣言を追加する(本文ラベル列は `VIII.` 付き)。
- `proof_obligations.md` に第VIII部の証明対象ラベル(定理4.2、5.2、7.3、8.5、8.6、系8.7、定理10.3、12.1、12.3、example theorem 群)を登録し、進行に応じて status を更新する。
- 定理候補5.5 / 6.3 / 6.5 / 8.10 / 9.2 / 10.4 / 10.7 は future proof obligation として登録するが、proved に昇格しない。
- 処遇表で「対象外」とした本文ラベルは台帳に登録しない。
- `GeneralPersistenceStability`, `GeneralZigzagStability`, `GeneralFlatBaseChangeForLawConflict`,
  `GeneralPerronFrobeniusHotspot`, `GeneralOptimalTransportTheory`, `AnalyticSmallnessImpliesLawfulness` は、
  本PRDでは未実装の future proof obligation または explicit non-goal として明記する。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは static finite measurement profile の理論を形式化する。第IX部の trace category、state transition presheaf、temporal coefficient、temporal law は扱わない。
- Finite AAT Computability は selected finite measurement regime と `EffCoeff_M` の範囲に限る。
  任意の site、任意の sheaf cohomology、任意の derived stack、任意の coefficient regime、任意の finitely generated module が計算可能であるとは主張しない。
- `measured_zero` は selected zero predicate の成立であり、unselected laws / supports / axes の zero を意味しない。
  `unmeasured` は zero ではなく、`unknown` は nonzero ではなく、`not_computed` は unmeasured と同じではない。
- `Zero_M` と `NonZero_M` は一般には論理補集合ではない。decidable complement を使う theorem は、別途 decidability / completeness assumption を要求する。
- analytic reading(distance、mass、rank、dimension、barcode、spectrum、residual norm、harmonic norm、Wasserstein cost)は structural verdict ではない。
  小さい analytic value や near-flatness から lawfulness を結論しない。
- Alexander dual の minimal hitting set は combinatorial repair target であり、actual architecture repair operation の legality、cost、side-effect、operation semantics を自動的には与えない。
- Stability theorem candidates は statement-only であり、本PRDの完了は persistence / zigzag / Morse / monotone witness stability の証明を含まない。
- Refactor invariance は selected measurement profile equivalence、coefficient iso、law ideal iso、witness / axis preservation に相対化される。
  syntax-level refactor や external rewrite が自動的に measurement-preserving であるとは主張しない。
- Cellular sheaf Laplacian、Hodge decomposition、harmonic debt minimality は finite-dimensional inner-product cochain model に相対化される。
  一般 Hilbert complex や infinite-dimensional analytic theory は扱わない。
- LawConflict measurement は common ambient pair がある場合だけ定義される。ambient / coefficient / topology が異なる場合、comparison morphism なしに Tor conflict を比較しない。
- Flat base change、transfer lower bound、Wasserstein lower bound、spectral hotspot は theorem candidate であり、non-flat base change や non-detecting pairing での保存 / 下界を主張しない。
- Support-localized transfer theorem は sufficient condition であり、すべての transfer residue を検出する necessary condition ではない。
- AAT-GAGA は selected finite measurement profile 内の comparison reading であり、外部 data source、外部 tool、任意の law universe、実務的品質判定の忠実性を主張しない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/Measurement` が新設され、CI の `lake build` でビルドされる。
      先行PRD依存の blocked 判定が運用されている(R0)
- [ ] AC2. `MeasurementProfile` と `Measured_M(alpha)` が形式化されている(R1)
- [ ] AC3. `MeasurementVerdict`、`VerdictData`、`StructuralVerdict`、`AnalyticReading` が形式化されている(R1)
- [ ] AC4. verdict boundary 補題(`unmeasured != measured_zero`、`unknown != measured_nonzero`、`not_computed != unmeasured`)が sorry なしで証明されている(R1)
- [ ] AC5. `FiniteMeasurementRegime` と `EffCoeff_M` interface が形式化されている(R2)
- [ ] AC6. 定理4.2 Finite AAT Computability が theorem package として sorry なしで証明されている(R2)
- [ ] AC7. Square-Free Repair Regime、Alexander dual、minimal hitting set が形式化されている(R3)
- [ ] AC8. 定理5.2 Stanley-Reisner / Alexander Dual Repair Theorem が sorry なしで証明されている(R3)
- [ ] AC9. Discrete Morse repair reading と定理候補5.5 statement がコンパイルされている(R3)
- [ ] AC10. Witness perturbation distance、persistence / zigzag profiles、定理候補6.3 / 6.5 statements がコンパイルされている(R4)
- [ ] AC11. Refactor morphism of measurement profiles と pullback of obstruction classes が形式化されている(R5)
- [ ] AC12. 定理7.3 Refactor Invariance under Equivalence が sorry なしで証明されている(R5)
- [ ] AC13. Cellular measurement model、sheaf Laplacian、distance-to-flatness reading が形式化されている(R6)
- [ ] AC14. 定理8.5 Finite Hodge Decomposition が sorry なしで証明されている(R6)
- [ ] AC15. 定理8.6 Harmonic Debt Minimality と系8.7 Essential Repair Lower Bound が sorry なしで証明されている(R6)
- [ ] AC16. Spectral gap reading、curvature transfer spectrum、定理候補8.10 statement が存在する(R6)
- [ ] AC17. Common ambient pair と LawConflict measurement が形式化され、定理候補9.2 flat base change statements がコンパイルされている(R7)
- [ ] AC18. Support-localized repair path、transfer measurement pairing が形式化されている(R8)
- [ ] AC19. 定理10.3 Support-Localized Transfer が sorry なしで証明されている(R8)
- [ ] AC20. Wasserstein transfer cost reading と定理候補10.4 / 10.7 statements が存在する(R8)
- [ ] AC21. `MeasurementPacket` が形式化され、certified readings と candidate interfaces が分離されている(R9)
- [ ] AC22. 定理12.1 Finite Measurement Synthesis が sorry なしで証明されている(R9)
- [ ] AC23. `AATGAGAComparisonPacket` が形式化されている(R10)
- [ ] AC24. 定理12.3 AAT-GAGA Finite Measurement Comparison が sorry なしで証明され、candidate-dependent fields が certified conclusions から分離されている(R10)
- [ ] AC25. 有限モデル拡張((a) pseudo-circle measurement、(b) square-free hitting set、(c) finite computability、
      (d) refactor invariance、(e) cellular Hodge、(f) support transfer、(g) measurement packet / AAT-GAGA)が検証されている(R11)
- [ ] AC26. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が存在しない
- [ ] AC27. `lean_theorem_index.md` の AG 節が第VIII部の宣言を `VIII.` 付き本文ラベルで含み、最終実装と一致している(R12)
- [ ] AC28. `proof_obligations.md` に第VIII部の証明対象ラベルが登録され、証明済み分が `proved`、theorem candidates と non-goals が future obligation / explicit non-goal として明記されている(R12)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2
   -> R3 -> R4
   -> R5
   -> R6
   -> R7 -> R8
   -> R9 -> R10
   -> R11 -> R12
```

R1/R2 は Part8 全体の型境界であり、最初に閉じる。
R3 は PRD-3 の Stanley-Reisner theorem に依存するが、Alexander dual / hitting set は有限組合せとして比較的独立に進められる。
R4 の stability は theorem candidate statement までに留め、証明済みタスクをブロックしない。
R6 は線形代数量が大きいため、まず finite cochain complex / adjoint / Laplacian の interface を閉じ、
低次 toy model で theorem shape を確認してから一般 theorem へ進む。
R7/R8 は PRD-5 の LawConflict / transfer pairing と接続するため、common ambient と support-localized predicate を先に固定する。
R9/R10 は最後に theorem package 化し、certified conclusion と candidate interface を混ぜない。
R11 の有限モデルは各ブロックが閉じるたびに増分追加してよい。
